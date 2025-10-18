/**
 * ZK Proof Aggregation Service
 * 
 * This service implements a cutting-edge zero-knowledge proof aggregation system that allows
 * proofs from multiple blockchains to be combined into a single verifiable credential.
 * 
 * Key features:
 * - Chain-agnostic verification protocol
 * - ZK-Proof attestations that hide sensitive vault data
 * - Proof aggregation to combine proofs from multiple chains
 */

import { createHash } from 'crypto';
import { BlockchainType } from '../../shared/types';
import { securityLogger } from '../monitoring/security-logger';
import { enhancedZeroKnowledgeService, EnhancedZkProof } from './enhanced-zero-knowledge-service';
import { crossChainErrorHandler, CrossChainErrorCategory } from '../security/cross-chain-error-handler';
import { ZkProofType, ZkProofResult } from './zero-knowledge-shield';

// Define the proof aggregation data structure
export interface AggregatedProof {
  id: string;
  timestamp: number;
  vaultId: string;
  chains: BlockchainType[];
  primaryChain: BlockchainType;
  proofs: Record<BlockchainType, EnhancedZkProof>;
  aggregationHash: string;
  validationThreshold: number;
  status: 'pending' | 'verified' | 'failed';
  validatedBy: BlockchainType[];
  metadata: Record<string, any>;
}

/**
 * ZK Proof Aggregation Service
 * Implements advanced zero-knowledge proof aggregation for cross-chain verification
 */
class ZkProofAggregation {
  private aggregatedProofs: Map<string, AggregatedProof> = new Map();
  
  constructor() {
    securityLogger.info('ZK Proof Aggregation service initialized');
  }
  
  /**
   * Aggregate zero-knowledge proofs from multiple chains into a single verifiable credential
   */
  async aggregateProofs(
    vaultId: string,
    proofs: Record<BlockchainType, EnhancedZkProof>,
    primaryChain: BlockchainType,
    metadata: Record<string, any> = {}
  ): Promise<AggregatedProof> {
    try {
      const chains = Object.keys(proofs) as BlockchainType[];
      
      if (chains.length === 0) {
        throw new Error('No proofs provided for aggregation');
      }
      
      if (!chains.includes(primaryChain)) {
        throw new Error(`Primary chain ${primaryChain} must be included in the proofs`);
      }
      
      securityLogger.info(`Aggregating ZK proofs for vault ${vaultId} across chains: ${chains.join(', ')}`);
      
      // Validate individual proofs first
      const validationResults = await this.validateIndividualProofs(proofs, vaultId);
      const validChains = Object.entries(validationResults)
        .filter(([_, result]) => result.success)
        .map(([chain]) => chain as BlockchainType);
      
      // Calculate threshold based on number of chains
      // Require at least 2 chains or 50% of chains, whichever is greater
      const validationThreshold = Math.max(2, Math.ceil(chains.length / 2));
      
      // Generate an aggregation hash that combines all proof data
      const aggregationHash = this.generateAggregationHash(proofs, vaultId);
      
      // Create the aggregated proof
      const aggregatedProof: AggregatedProof = {
        id: `zkp-agg-${Date.now()}-${vaultId}`,
        timestamp: Date.now(),
        vaultId,
        chains,
        primaryChain,
        proofs,
        aggregationHash,
        validationThreshold,
        status: validChains.length >= validationThreshold ? 'verified' : 'pending',
        validatedBy: validChains,
        metadata: {
          ...metadata,
          validationResults
        }
      };
      
      // Store the aggregated proof
      this.aggregatedProofs.set(aggregatedProof.id, aggregatedProof);
      
      securityLogger.info(
        `ZK proof aggregation complete for vault ${vaultId}. Status: ${aggregatedProof.status}`,
        {
          vaultId,
          aggregatedProofId: aggregatedProof.id,
          validChains: validChains.length,
          threshold: validationThreshold
        }
      );
      
      return aggregatedProof;
    } catch (error) {
      // Handle unexpected errors
      const crossChainError = crossChainErrorHandler.handle(error, {
        category: CrossChainErrorCategory.VALIDATION_FAILURE,
        blockchain: primaryChain
      });
      
      securityLogger.error(`ZK proof aggregation failed for vault ${vaultId}`, {
        vaultId,
        errorCategory: crossChainError.category,
        errorMessage: crossChainError.message
      });
      
      throw new Error(`ZK proof aggregation failed: ${crossChainError.message}`);
    }
  }
  
  /**
   * Validate all individual proofs before aggregation
   */
  private async validateIndividualProofs(
    proofs: Record<BlockchainType, EnhancedZkProof>,
    vaultId: string
  ): Promise<Record<BlockchainType, ZkProofResult>> {
    const chains = Object.keys(proofs) as BlockchainType[];
    const results: Record<BlockchainType, ZkProofResult> = {} as any;
    
    // Validate each proof in parallel
    await Promise.all(chains.map(async (chain) => {
      try {
        const result = await enhancedZeroKnowledgeService.verifyEnhancedProof(
          proofs[chain],
          ZkProofType.CROSS_CHAIN,
          chain
        );
        results[chain] = result;
      } catch (error) {
        securityLogger.warn(`Failed to verify proof for chain ${chain}`, {
          vaultId,
          chain,
          error
        });
        
        // Add a failed verification result
        results[chain] = {
          success: false,
          proofType: ZkProofType.CROSS_CHAIN,
          timestamp: Date.now(),
          publicInputHash: '',
          blockchainType: chain,
          verificationMethod: 'verification-failed'
        };
      }
    }));
    
    return results;
  }
  
  /**
   * Generate a cryptographic hash that aggregates all proof data
   */
  private generateAggregationHash(
    proofs: Record<BlockchainType, EnhancedZkProof>,
    vaultId: string
  ): string {
    const chains = Object.keys(proofs) as BlockchainType[];
    
    // Create a deterministic ordering of chains
    const orderedChains = [...chains].sort();
    
    // Combine proof data in a deterministic way
    const proofData = orderedChains.map(chain => {
      const proof = proofs[chain];
      return `${chain}:${proof.proof}:${proof.publicInputs.join(':')}:${proof.verificationKey}`;
    }).join('|');
    
    // Create the aggregation hash
    const aggregationData = `${vaultId}:${proofData}:${Date.now()}`;
    return createHash('sha256').update(aggregationData).digest('hex');
  }
  
  /**
   * Get an aggregated proof by ID
   */
  getAggregatedProof(id: string): AggregatedProof | undefined {
    return this.aggregatedProofs.get(id);
  }
  
  /**
   * Validate an aggregated proof
   * Returns true if the proof is valid according to the threshold
   */
  validateAggregatedProof(id: string): boolean {
    const proof = this.aggregatedProofs.get(id);
    
    if (!proof) {
      return false;
    }
    
    return proof.validatedBy.length >= proof.validationThreshold;
  }
  
  /**
   * Add a new chain validation to an existing aggregated proof
   */
  async addChainValidation(
    id: string,
    chain: BlockchainType,
    proof: EnhancedZkProof
  ): Promise<AggregatedProof> {
    const aggregatedProof = this.aggregatedProofs.get(id);
    
    if (!aggregatedProof) {
      throw new Error(`Aggregated proof ${id} not found`);
    }
    
    // Verify the new proof
    const verificationResult = await enhancedZeroKnowledgeService.verifyEnhancedProof(
      proof,
      ZkProofType.CROSS_CHAIN,
      chain
    );
    
    if (verificationResult.success) {
      // Add the chain to the validated list if not already present
      if (!aggregatedProof.validatedBy.includes(chain)) {
        aggregatedProof.validatedBy.push(chain);
      }
      
      // Add the proof to the proofs collection
      aggregatedProof.proofs[chain] = proof;
      
      // Update the status if we've passed the threshold
      if (aggregatedProof.validatedBy.length >= aggregatedProof.validationThreshold && 
          aggregatedProof.status !== 'verified') {
        aggregatedProof.status = 'verified';
        
        securityLogger.info(`Aggregated proof ${id} is now verified`, {
          vaultId: aggregatedProof.vaultId,
          validChains: aggregatedProof.validatedBy.length,
          threshold: aggregatedProof.validationThreshold
        });
      }
      
      // Update the stored proof
      this.aggregatedProofs.set(id, aggregatedProof);
    } else {
      securityLogger.warn(`Validation failed for chain ${chain} on aggregated proof ${id}`, {
        vaultId: aggregatedProof.vaultId,
        chain
      });
    }
    
    return aggregatedProof;
  }
}

// Export a singleton instance for use throughout the application
export const zkProofAggregation = new ZkProofAggregation();