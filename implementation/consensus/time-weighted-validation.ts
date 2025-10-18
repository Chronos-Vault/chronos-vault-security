/**
 * Time-Weighted Validation
 * 
 * This module implements a time-weighted validation system that adjusts
 * security requirements based on vault value and time sensitivity.
 * Higher-value vaults require more validation confirmations and longer
 * time windows for security.
 */

import { BlockchainType } from '../../shared/types';
import { securityLogger } from '../monitoring/security-logger';
import { stateMerkleTreeService, StateLeaf } from './state-merkle-tree';

// Define validation tiers based on vault value
export enum ValidationTier {
  STANDARD = 'standard',
  ENHANCED = 'enhanced',
  PREMIUM = 'premium',
  MAXIMUM = 'maximum'
}

// Define the validation requirements for each tier
export interface ValidationRequirements {
  minimumConfirmations: number;
  requiredChains: number;
  timeWindowSeconds: number;
  merkleProofRequired: boolean;
  doubleSignatureRequired: boolean;
}

// Define a validation request
export interface TimeWeightedValidationRequest {
  vaultId: string;
  value: number; // In USD
  primaryChain: BlockchainType;
  requestTimestamp: number;
  merkleRoot?: string;
  requestMetadata?: Record<string, any>;
}

// Define a validation confirmation
export interface ValidationConfirmation {
  vaultId: string;
  chain: BlockchainType;
  confirmationTimestamp: number;
  validatorSignature?: string;
  stateLeaf?: StateLeaf;
  blockHeight?: number;
  transactionId?: string;
}

// Define a validation result
export interface ValidationResult {
  vaultId: string;
  tier: ValidationTier;
  requirements: ValidationRequirements;
  isValid: boolean;
  confirmedChains: BlockchainType[];
  missingChains: BlockchainType[];
  confirmations: ValidationConfirmation[];
  timeWindowComplete: boolean;
  merkleProofVerified: boolean;
  resultTimestamp: number;
  metadata: Record<string, any>;
}

/**
 * Time-Weighted Validation Service
 * 
 * Implements a validation system that scales security requirements
 * based on vault value and time sensitivity
 */
class TimeWeightedValidationService {
  private validationRequests: Map<string, TimeWeightedValidationRequest> = new Map();
  private validationConfirmations: Map<string, ValidationConfirmation[]> = new Map();
  private validationResults: Map<string, ValidationResult> = new Map();
  
  constructor() {
    securityLogger.info('Time-Weighted Validation service initialized');
  }
  
  /**
   * Get the validation tier based on vault value
   */
  getValidationTier(valueUSD: number): ValidationTier {
    if (valueUSD >= 1000000) {
      return ValidationTier.MAXIMUM;
    } else if (valueUSD >= 100000) {
      return ValidationTier.PREMIUM;
    } else if (valueUSD >= 10000) {
      return ValidationTier.ENHANCED;
    } else {
      return ValidationTier.STANDARD;
    }
  }
  
  /**
   * Get the validation requirements for a tier
   */
  getValidationRequirements(tier: ValidationTier): ValidationRequirements {
    switch (tier) {
      case ValidationTier.MAXIMUM:
        return {
          minimumConfirmations: 12,
          requiredChains: 4, // All chains
          timeWindowSeconds: 7200, // 2 hours
          merkleProofRequired: true,
          doubleSignatureRequired: true
        };
      case ValidationTier.PREMIUM:
        return {
          minimumConfirmations: 8,
          requiredChains: 3,
          timeWindowSeconds: 3600, // 1 hour
          merkleProofRequired: true,
          doubleSignatureRequired: false
        };
      case ValidationTier.ENHANCED:
        return {
          minimumConfirmations: 6,
          requiredChains: 2,
          timeWindowSeconds: 1800, // 30 minutes
          merkleProofRequired: true,
          doubleSignatureRequired: false
        };
      case ValidationTier.STANDARD:
      default:
        return {
          minimumConfirmations: 3,
          requiredChains: 1,
          timeWindowSeconds: 600, // 10 minutes
          merkleProofRequired: false,
          doubleSignatureRequired: false
        };
    }
  }
  
  /**
   * Start a validation request for a vault
   */
  initiateValidation(request: TimeWeightedValidationRequest): ValidationResult {
    const vaultId = request.vaultId;
    const tier = this.getValidationTier(request.value);
    const requirements = this.getValidationRequirements(tier);
    
    // Store the request
    this.validationRequests.set(vaultId, {
      ...request,
      requestTimestamp: Date.now()
    });
    
    // Initialize confirmations array
    this.validationConfirmations.set(vaultId, []);
    
    // Create an initial result
    const result: ValidationResult = {
      vaultId,
      tier,
      requirements,
      isValid: false,
      confirmedChains: [],
      missingChains: this.getRequiredChains(request.primaryChain, requirements.requiredChains),
      confirmations: [],
      timeWindowComplete: false,
      merkleProofVerified: false,
      resultTimestamp: Date.now(),
      metadata: {
        initiatedAt: Date.now(),
        valueUSD: request.value,
        primaryChain: request.primaryChain,
        ...request.requestMetadata
      }
    };
    
    // Store the result
    this.validationResults.set(vaultId, result);
    
    securityLogger.info(`Initiated time-weighted validation for vault ${vaultId}`, {
      vaultId,
      tier,
      valueUSD: request.value,
      requiredChains: requirements.requiredChains
    });
    
    return result;
  }
  
  /**
   * Get the required chains for validation
   */
  private getRequiredChains(primaryChain: BlockchainType, count: number): BlockchainType[] {
    const allChains: BlockchainType[] = ['ETH', 'SOL', 'TON', 'BTC'];
    
    // Ensure the primary chain is always included
    const requiredChains = [primaryChain];
    
    // Add additional chains up to the required count
    const otherChains = allChains.filter(chain => chain !== primaryChain);
    for (let i = 0; i < Math.min(count - 1, otherChains.length); i++) {
      requiredChains.push(otherChains[i]);
    }
    
    return requiredChains;
  }
  
  /**
   * Add a validation confirmation for a chain
   */
  addConfirmation(confirmation: ValidationConfirmation): ValidationResult | null {
    const vaultId = confirmation.vaultId;
    const request = this.validationRequests.get(vaultId);
    
    if (!request) {
      securityLogger.warn(`No validation request found for vault ${vaultId}`);
      return null;
    }
    
    // Get current confirmations
    const confirmations = this.validationConfirmations.get(vaultId) || [];
    confirmations.push(confirmation);
    this.validationConfirmations.set(vaultId, confirmations);
    
    // Update the validation result
    return this.updateValidation(vaultId);
  }
  
  /**
   * Update the validation result based on current confirmations
   */
  updateValidation(vaultId: string): ValidationResult | null {
    const request = this.validationRequests.get(vaultId);
    const confirmations = this.validationConfirmations.get(vaultId) || [];
    let result = this.validationResults.get(vaultId);
    
    if (!request || !result) {
      return null;
    }
    
    const tier = this.getValidationTier(request.value);
    const requirements = this.getValidationRequirements(tier);
    
    // Calculate confirmed chains
    const confirmedChains: BlockchainType[] = [];
    for (const confirmation of confirmations) {
      if (!confirmedChains.includes(confirmation.chain)) {
        confirmedChains.push(confirmation.chain);
      }
    }
    
    // Calculate missing chains
    const requiredChains = this.getRequiredChains(request.primaryChain, requirements.requiredChains);
    const missingChains = requiredChains.filter(chain => !confirmedChains.includes(chain));
    
    // Check if time window is complete
    const currentTime = Date.now();
    const timeWindowComplete = (currentTime - request.requestTimestamp) >= requirements.timeWindowSeconds * 1000;
    
    // Check Merkle proof if required
    let merkleProofVerified = !requirements.merkleProofRequired;
    if (requirements.merkleProofRequired && request.merkleRoot) {
      // Verify each chain's state is consistent with the Merkle root
      const snapshot = stateMerkleTreeService.getVaultStateSnapshot(vaultId);
      merkleProofVerified = Boolean(snapshot && snapshot.rootHash === request.merkleRoot);
    }
    
    // Determine if validation is successful
    const isValid = confirmedChains.length >= requirements.requiredChains &&
                    timeWindowComplete &&
                    merkleProofVerified;
    
    // Update the result
    result = {
      ...result,
      tier,
      requirements,
      isValid,
      confirmedChains,
      missingChains,
      confirmations,
      timeWindowComplete,
      merkleProofVerified,
      resultTimestamp: currentTime,
      metadata: {
        ...result.metadata,
        lastUpdated: currentTime
      }
    };
    
    this.validationResults.set(vaultId, result);
    
    securityLogger.info(`Updated validation for vault ${vaultId}`, {
      vaultId,
      isValid,
      confirmedChains: confirmedChains.length,
      requiredChains: requirements.requiredChains,
      timeWindowComplete,
      merkleProofVerified
    });
    
    return result;
  }
  
  /**
   * Get the current validation result for a vault
   */
  getValidationResult(vaultId: string): ValidationResult | null {
    return this.validationResults.get(vaultId) || null;
  }
  
  /**
   * Check if a validation is complete and successful
   */
  isValidationComplete(vaultId: string): boolean {
    const result = this.validationResults.get(vaultId);
    return Boolean(result && result.isValid);
  }
}

// Export a singleton instance
export const timeWeightedValidation = new TimeWeightedValidationService();