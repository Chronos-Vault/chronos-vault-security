/**
 * Chain-Agnostic Verification Protocol
 * 
 * This module implements a unified verification protocol that works across different blockchains,
 * enabling consistent verification regardless of the underlying blockchain technology.
 * 
 * Key features:
 * - Common verification interface across all supported chains
 * - Standardized proof format that can be verified on any supported chain
 * - Support for cross-chain verification without revealing sensitive vault data
 */

import { BlockchainType } from '../../shared/types';
import { securityLogger } from '../monitoring/security-logger';
import { crossChainErrorHandler, CrossChainErrorCategory } from '../security/cross-chain-error-handler';
import { ConnectorFactory } from '../blockchain/connector-factory';
import { enhancedZeroKnowledgeService, EnhancedZkProof } from './enhanced-zero-knowledge-service';
import { zkProofAggregation, AggregatedProof } from './zk-proof-aggregation';
import { ZkProofType } from './zero-knowledge-shield';

// Chain-agnostic verification request format
export interface VerificationRequest {
  vaultId: string;
  ownerAddress: string;
  nonce: string;
  timestamp: number;
  blockchainType: BlockchainType;
  verificationLevel: 'basic' | 'standard' | 'advanced';
  metadata?: Record<string, any>;
}

// Chain-agnostic verification response format
export interface VerificationResponse {
  success: boolean;
  vaultId: string;
  timestamp: number;
  verificationId: string;
  proofId?: string;
  aggregatedProofId?: string;
  chains: BlockchainType[];
  errors?: Record<string, string>;
  metadata?: Record<string, any>;
}

/**
 * Chain-Agnostic Verification Protocol
 * Implements a standardized verification interface across all supported blockchains
 */
class ChainAgnosticVerification {
  private connectorFactory: ConnectorFactory;
  private verificationCache: Map<string, VerificationResponse> = new Map();
  
  constructor(connectorFactory: ConnectorFactory) {
    this.connectorFactory = connectorFactory;
    securityLogger.info('Chain-Agnostic Verification Protocol initialized');
  }
  
  /**
   * Verify a vault using the chain-agnostic protocol
   */
  async verifyVault(request: VerificationRequest): Promise<VerificationResponse> {
    const { vaultId, blockchainType, verificationLevel } = request;
    
    try {
      securityLogger.info(`Chain-agnostic verification requested for vault ${vaultId}`, {
        vaultId,
        primaryChain: blockchainType,
        level: verificationLevel
      });
      
      // Create a unique verification ID
      const verificationId = `verification-${Date.now()}-${vaultId}`;
      
      // Determine which chains to verify based on the verification level
      const chains = this.getChainsForVerificationLevel(blockchainType, verificationLevel);
      
      securityLogger.info(`Verifying vault ${vaultId} across chains: ${chains.join(', ')}`);
      
      // Generate zero-knowledge proofs for each chain
      const proofs: Record<BlockchainType, EnhancedZkProof> = {};
      const errors: Record<string, string> = {};
      
      // Generate proofs in parallel for better performance
      await Promise.all(chains.map(async (chain) => {
        try {
          // For each chain, we need to generate a specific proof
          const proof = await this.generateChainSpecificProof(vaultId, request, chain);
          proofs[chain] = proof;
        } catch (error) {
          const errorMessage = error instanceof Error ? error.message : 'Unknown error';
          securityLogger.warn(`Failed to generate proof for chain ${chain}`, {
            vaultId,
            chain,
            error: errorMessage
          });
          
          errors[chain] = errorMessage;
        }
      }));
      
      // Determine if we have enough successful proofs
      const successfulChains = Object.keys(proofs) as BlockchainType[];
      const requiredChains = this.getRequiredChainsCount(verificationLevel);
      
      if (successfulChains.length < requiredChains) {
        // Not enough successful proofs
        const response: VerificationResponse = {
          success: false,
          vaultId,
          timestamp: Date.now(),
          verificationId,
          chains: successfulChains,
          errors,
          metadata: {
            requiredChains,
            successfulChains: successfulChains.length,
            message: `Insufficient successful verifications. Required: ${requiredChains}, Got: ${successfulChains.length}`
          }
        };
        
        this.verificationCache.set(verificationId, response);
        return response;
      }
      
      // Aggregate the proofs into a single verifiable credential
      const aggregatedProof = await zkProofAggregation.aggregateProofs(
        vaultId,
        proofs,
        blockchainType,
        { verificationLevel, ...request.metadata }
      );
      
      // Prepare the response
      const response: VerificationResponse = {
        success: aggregatedProof.status === 'verified',
        vaultId,
        timestamp: Date.now(),
        verificationId,
        proofId: Object.values(proofs)[0]?.proof,
        aggregatedProofId: aggregatedProof.id,
        chains: successfulChains,
        metadata: {
          aggregatedProof: {
            id: aggregatedProof.id,
            status: aggregatedProof.status,
            validationThreshold: aggregatedProof.validationThreshold,
            validatedBy: aggregatedProof.validatedBy
          }
        }
      };
      
      if (Object.keys(errors).length > 0) {
        response.errors = errors;
      }
      
      this.verificationCache.set(verificationId, response);
      
      securityLogger.info(`Chain-agnostic verification completed for vault ${vaultId}`, {
        vaultId,
        verificationId,
        success: response.success,
        chains: successfulChains
      });
      
      return response;
    } catch (error) {
      // Handle unexpected errors
      const crossChainError = crossChainErrorHandler.handle(error, {
        category: CrossChainErrorCategory.VALIDATION_FAILURE,
        blockchain: blockchainType
      });
      
      securityLogger.error(`Chain-agnostic verification failed for vault ${vaultId}`, {
        vaultId,
        errorCategory: crossChainError.category,
        errorMessage: crossChainError.message
      });
      
      // Create an error response
      const errorResponse: VerificationResponse = {
        success: false,
        vaultId,
        timestamp: Date.now(),
        verificationId: `error-${Date.now()}-${vaultId}`,
        chains: [],
        errors: {
          general: crossChainError.message
        },
        metadata: {
          errorCategory: crossChainError.category
        }
      };
      
      return errorResponse;
    }
  }
  
  /**
   * Generate a chain-specific proof for verification
   */
  private async generateChainSpecificProof(
    vaultId: string,
    request: VerificationRequest,
    chain: BlockchainType
  ): Promise<EnhancedZkProof> {
    try {
      // Get the blockchain connector for this chain
      const connector = this.connectorFactory.getConnector(chain);
      
      // Check if the chain is available
      const isAvailable = await connector.isAvailable();
      if (!isAvailable) {
        throw new Error(`Chain ${chain} is not available`);
      }
      
      // Generate a private key hash that we'll use for the ZK proof
      // This is a simulated private key for demonstration purposes
      // In production, this would be derived from the user's wallet or encryption key
      const privateKeyHash = `${request.ownerAddress}-${request.nonce}-${chain}`;
      
      // Generate the chain-specific proof
      return await enhancedZeroKnowledgeService.generateVaultOwnershipProof(
        vaultId,
        request.ownerAddress,
        privateKeyHash,
        chain
      );
    } catch (error) {
      securityLogger.error(`Failed to generate chain-specific proof for ${chain}`, {
        vaultId,
        chain,
        error
      });
      
      throw error;
    }
  }
  
  /**
   * Determine which chains to use for verification based on the level
   */
  private getChainsForVerificationLevel(
    primaryChain: BlockchainType,
    level: 'basic' | 'standard' | 'advanced'
  ): BlockchainType[] {
    // Default to all supported chains
    const allChains: BlockchainType[] = ['ETH', 'SOL', 'TON', 'BTC'];
    
    // Remove the primary chain from the list to avoid duplication
    const secondaryChains = allChains.filter(chain => chain !== primaryChain);
    
    switch (level) {
      case 'basic':
        // Basic verification only uses the primary chain
        return [primaryChain];
        
      case 'standard':
        // Standard verification uses the primary chain plus one secondary chain
        return [primaryChain, secondaryChains[0]];
        
      case 'advanced':
        // Advanced verification uses all available chains
        return [primaryChain, ...secondaryChains];
        
      default:
        return [primaryChain];
    }
  }
  
  /**
   * Get the required number of chains for successful verification
   */
  private getRequiredChainsCount(level: 'basic' | 'standard' | 'advanced'): number {
    switch (level) {
      case 'basic':
        return 1; // Just the primary chain
      case 'standard':
        return 2; // Primary plus one secondary
      case 'advanced':
        return 3; // Primary plus at least two secondary
      default:
        return 1;
    }
  }
  
  /**
   * Get a cached verification response
   */
  getVerification(verificationId: string): VerificationResponse | undefined {
    return this.verificationCache.get(verificationId);
  }
}

// Export the factory function to create instances
export function createChainAgnosticVerification(connectorFactory: ConnectorFactory): ChainAgnosticVerification {
  return new ChainAgnosticVerification(connectorFactory);
}