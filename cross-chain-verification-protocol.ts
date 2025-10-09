/**
 * Cross-Chain Verification Protocol
 * 
 * This module provides a comprehensive verification protocol for cross-chain
 * vault operations, ensuring vault security through multi-chain verification.
 * It implements the Triple-Chain Security architecture of Chronos Vault.
 */

import { securityLogger } from '../monitoring/security-logger';
import { ethersClient } from '../blockchain/ethereum-client';
import { solanaClient } from '../blockchain/solana-client';
import { tonClient } from '../blockchain/ton-client';
import { BlockchainType } from '../../shared/types';
import config from '../config';
import { 
  BlockchainError, 
  BlockchainErrorCategory,
  createBlockchainError,
  withBlockchainErrorHandling 
} from '../blockchain/enhanced-error-handling';
import { crossChainBridge } from '../blockchain/cross-chain-bridge';
import { bitcoinService } from '../blockchain/bitcoin-service';

// Interface for verification results
export interface VerificationResult {
  success: boolean;
  message: string;
  data?: any;
  timestamp: number;
}

// Interface for multi-chain verification results
export interface MultiChainVerificationResult {
  success: boolean;
  message: string;
  chains: Record<BlockchainType, {
    verified: boolean;
    confirmations: number;
    message: string;
    timestamp: number;
  }>;
  overallConfidence: number;
  timestamp: number;
}

class CrossChainVerificationProtocol {
  private initialized = false;
  
  /**
   * Initialize the verification protocol
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }
    
    try {
      securityLogger.info('Initializing cross-chain verification protocol');
      
      // Initialize blockchain clients
      if (!ethersClient.isInitialized()) {
        await ethersClient.initialize();
      }
      
      if (!solanaClient.isInitialized()) {
        await solanaClient.initialize();
      }
      
      if (!tonClient.isInitialized()) {
        await tonClient.initialize();
      }
      
      if (!crossChainBridge.isInitialized()) {
        await crossChainBridge.initialize();
      }
      
      this.initialized = true;
      securityLogger.info('Cross-chain verification protocol initialized successfully');
    } catch (error) {
      securityLogger.error('Failed to initialize cross-chain verification protocol', error);
      throw error;
    }
  }
  
  /**
   * Check if the protocol is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }
  
  /**
   * Verify a vault on a specific blockchain
   */
  async verifyVaultExists(
    vaultId: string,
    blockchain: BlockchainType
  ): Promise<VerificationResult> {
    if (!this.initialized) {
      await this.initialize();
    }
    
    try {
      securityLogger.info(`Verifying vault ${vaultId} on ${blockchain}`);
      
      let exists = false;
      let confirmations = 0;
      let owner = '';
      
      // Check for vault on the specified blockchain
      if (blockchain === 'ETH') {
        const result = await ethersClient.verifyVaultExists(vaultId);
        exists = result.exists;
        confirmations = result.confirmations;
        owner = result.owner;
      } else if (blockchain === 'SOL') {
        const result = await solanaClient.verifyVaultExists(vaultId);
        exists = result.exists;
        confirmations = result.confirmations;
        owner = result.owner;
      } else if (blockchain === 'TON') {
        const result = await tonClient.verifyVaultExists(vaultId);
        exists = result.exists;
        confirmations = result.confirmations;
        owner = result.owner;
      } else if (blockchain === 'BTC') {
        // For Bitcoin, we don't have native vault functionality yet
        // This is a placeholder for future integration
        if (config.isDevelopmentMode) {
          exists = true;
          confirmations = 6;
          owner = `btc-dev-owner-${Date.now()}`;
        } else {
          throw new Error("Bitcoin vault verification not yet implemented");
        }
      } else {
        throw new Error(`Unsupported blockchain: ${blockchain}`);
      }
      
      if (exists) {
        return {
          success: true,
          message: `Vault ${vaultId} verified on ${blockchain} with ${confirmations} confirmations`,
          data: {
            vaultId,
            blockchain,
            confirmations,
            owner
          },
          timestamp: Date.now()
        };
      } else {
        return {
          success: false,
          message: `Vault ${vaultId} not found on ${blockchain}`,
          timestamp: Date.now()
        };
      }
    } catch (error) {
      securityLogger.error(`Failed to verify vault ${vaultId} on ${blockchain}`, error);
      
      if (error instanceof BlockchainError) {
        throw error;
      }
      
      throw createBlockchainError(
        error,
        blockchain,
        BlockchainErrorCategory.VALIDATION,
        {
          vaultId,
          operation: 'verifyVaultExists'
        }
      );
    }
  }
  
  /**
   * Verify a vault across multiple blockchains
   */
  async verifyVaultAcrossChains(
    vaultId: string,
    primaryChain: BlockchainType,
    secondaryChains: BlockchainType[]
  ): Promise<MultiChainVerificationResult> {
    if (!this.initialized) {
      await this.initialize();
    }
    
    try {
      securityLogger.info(`Verifying vault ${vaultId} across chains`, {
        primaryChain,
        secondaryChains
      });
      
      // Check primary chain first
      const primaryResult = await this.verifyVaultExists(vaultId, primaryChain);
      
      if (!primaryResult.success) {
        // If the vault doesn't exist on the primary chain, consider it a failure
        const results: Record<BlockchainType, any> = {} as any;
        results[primaryChain] = {
          verified: false,
          confirmations: 0,
          message: `Vault not found on primary chain ${primaryChain}`,
          timestamp: Date.now()
        };
        
        return {
          success: false,
          message: `Vault ${vaultId} not found on primary chain ${primaryChain}`,
          chains: results,
          overallConfidence: 0,
          timestamp: Date.now()
        };
      }
      
      // Store the results for each chain
      const results: Record<BlockchainType, any> = {} as any;
      results[primaryChain] = {
        verified: true,
        confirmations: primaryResult.data.confirmations,
        message: primaryResult.message,
        timestamp: primaryResult.timestamp
      };
      
      // Check secondary chains
      const chainPromises = secondaryChains.map(async (chain) => {
        try {
          // For development mode, simulate verification
          if (config.isDevelopmentMode) {
            // Simplify by assuming secondary chains match in dev mode
            results[chain] = {
              verified: true,
              confirmations: Math.floor(Math.random() * 30) + 1,
              message: `Vault ${vaultId} verified on ${chain} in development mode`,
              timestamp: Date.now()
            };
            return;
          }
          
          const result = await this.verifyVaultExists(vaultId, chain);
          results[chain] = {
            verified: result.success,
            confirmations: result.success ? result.data.confirmations : 0,
            message: result.message,
            timestamp: result.timestamp
          };
        } catch (error) {
          securityLogger.error(`Error verifying vault on ${chain}`, error);
          results[chain] = {
            verified: false,
            confirmations: 0,
            message: error instanceof Error ? error.message : "Unknown error",
            timestamp: Date.now()
          };
        }
      });
      
      // Wait for all chain verifications to complete
      await Promise.all(chainPromises);
      
      // Calculate overall confidence based on verification results
      const verifiedChains = Object.values(results).filter(r => r.verified).length;
      const totalChains = Object.keys(results).length;
      const overallConfidence = totalChains > 0 ? verifiedChains / totalChains : 0;
      
      // Determine success based on confidence threshold
      const confidenceThreshold = config.security.crossChain.verificationThreshold || 0.51; // Default to majority
      const success = overallConfidence >= confidenceThreshold;
      
      return {
        success,
        message: success 
          ? `Vault ${vaultId} verified across ${verifiedChains}/${totalChains} chains` 
          : `Vault ${vaultId} verification failed on majority of chains`,
        chains: results,
        overallConfidence,
        timestamp: Date.now()
      };
    } catch (error) {
      securityLogger.error(`Failed to verify vault ${vaultId} across chains`, error);
      
      if (error instanceof BlockchainError) {
        throw error;
      }
      
      throw createBlockchainError(
        error,
        primaryChain,
        BlockchainErrorCategory.CROSS_CHAIN,
        {
          vaultId,
          primaryChain,
          secondaryChains,
          operation: 'verifyVaultAcrossChains'
        }
      );
    }
  }
  
  /**
   * Create cross-chain verification proofs
   */
  async createVerificationProofs(
    vaultId: string,
    primaryChain: BlockchainType,
    secondaryChains: BlockchainType[]
  ): Promise<{
    success: boolean;
    proofs: any[];
    message: string;
  }> {
    if (!this.initialized) {
      await this.initialize();
    }
    
    try {
      // Delegate to bridge service for proof creation
      return await crossChainBridge.createCrossChainProof(
        vaultId,
        primaryChain,
        secondaryChains
      );
    } catch (error) {
      securityLogger.error(`Failed to create verification proofs for vault ${vaultId}`, error);
      
      if (error instanceof BlockchainError) {
        throw error;
      }
      
      throw createBlockchainError(
        error,
        primaryChain,
        BlockchainErrorCategory.CROSS_CHAIN,
        {
          vaultId,
          primaryChain,
          secondaryChains,
          operation: 'createVerificationProofs'
        }
      );
    }
  }
  
  /**
   * Check the full security status of a vault across all chains
   */
  async checkVaultSecurityStatus(
    vaultId: string,
    primaryChain: BlockchainType
  ): Promise<{
    success: boolean;
    securityLevel: number;
    riskFactors: string[];
    verificationResults: MultiChainVerificationResult;
    recommendations: string[];
  }> {
    if (!this.initialized) {
      await this.initialize();
    }
    
    try {
      // Define the verification chains
      const secondaryChains: BlockchainType[] = ['ETH', 'SOL', 'TON'].filter(
        chain => chain !== primaryChain
      ) as BlockchainType[];
      
      // Verify the vault across chains
      const verificationResults = await this.verifyVaultAcrossChains(
        vaultId,
        primaryChain,
        secondaryChains
      );
      
      // Analyze security based on verification results
      const riskFactors: string[] = [];
      let securityLevel = 3; // Start with highest security
      
      // Check verification confidence
      if (verificationResults.overallConfidence < 1.0) {
        riskFactors.push('Not all chains have verified the vault');
        securityLevel = Math.min(securityLevel, 2);
      }
      
      // Check confirmations on primary chain
      const primaryConfirmations = verificationResults.chains[primaryChain].confirmations;
      const minConfirmations = config.security.minConfirmations[primaryChain] || 12;
      
      if (primaryConfirmations < minConfirmations) {
        riskFactors.push(`Primary chain has only ${primaryConfirmations}/${minConfirmations} recommended confirmations`);
        securityLevel = Math.min(securityLevel, 2);
      }
      
      // Check if any secondary chains failed verification
      const failedChains = secondaryChains.filter(
        chain => !verificationResults.chains[chain]?.verified
      );
      
      if (failedChains.length > 0) {
        riskFactors.push(`Verification failed on secondary chains: ${failedChains.join(', ')}`);
        securityLevel = Math.min(securityLevel, 1);
      }
      
      // Generate recommendations based on risk factors
      const recommendations: string[] = [];
      
      if (riskFactors.length === 0) {
        recommendations.push('No action needed. Vault has maximum security.');
      } else {
        if (failedChains.length > 0) {
          recommendations.push(`Re-initialize cross-chain verification for ${failedChains.join(', ')}`);
        }
        
        if (primaryConfirmations < minConfirmations) {
          recommendations.push(`Wait for additional confirmations on ${primaryChain} (currently ${primaryConfirmations}/${minConfirmations})`);
        }
        
        if (verificationResults.overallConfidence < 1.0) {
          recommendations.push('Verify vault integrity across all chains');
        }
      }
      
      return {
        success: verificationResults.success,
        securityLevel,
        riskFactors,
        verificationResults,
        recommendations
      };
    } catch (error) {
      securityLogger.error(`Failed to check vault security status for ${vaultId}`, error);
      
      if (error instanceof BlockchainError) {
        throw error;
      }
      
      throw createBlockchainError(
        error,
        primaryChain,
        BlockchainErrorCategory.CROSS_CHAIN,
        {
          vaultId,
          primaryChain,
          operation: 'checkVaultSecurityStatus'
        }
      );
    }
  }
}

export const crossChainVerification = new CrossChainVerificationProtocol();