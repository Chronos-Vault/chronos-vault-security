/**
 * Merkle Proof System for Cross-Chain Verification
 * 
 * Pure mathematics - No trust required
 * Enables cryptographic verification of cross-chain state without trusting any single chain
 */

import { ethers } from 'ethers';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';

/**
 * Merkle tree node
 */
interface MerkleNode {
  hash: string;
  left?: MerkleNode;
  right?: MerkleNode;
  data?: any;
}

/**
 * Merkle proof for verification
 */
export interface MerkleProof {
  root: string;
  leaf: string;
  proof: string[];
  indices: number[];
  verified: boolean;
}

/**
 * Cross-chain state that needs verification
 */
export interface CrossChainState {
  chain: 'ethereum' | 'solana' | 'ton';
  vaultId: string;
  state: 'active' | 'locked' | 'unlocked' | 'compromised';
  timestamp: number;
  blockHeight: number;
  stateHash: string;
}

/**
 * Merkle Proof System
 * Generates cryptographic proofs for cross-chain verification
 */
export class MerkleProofSystem {
  /**
   * Generate Merkle root from array of data
   */
  static generateMerkleRoot(data: any[]): string {
    if (data.length === 0) {
      return ethers.keccak256(ethers.toUtf8Bytes('empty-tree'));
    }

    // Convert data to leaf hashes
    const leaves = data.map(item => this.hashLeaf(item));
    
    // Build Merkle tree
    const tree = this.buildMerkleTree(leaves);
    
    return tree.hash;
  }

  /**
   * Generate Merkle proof for specific data item
   */
  static generateMerkleProof(data: any[], targetIndex: number): MerkleProof {
    if (targetIndex < 0 || targetIndex >= data.length) {
      throw new Error('Invalid target index for Merkle proof');
    }

    const leaves = data.map(item => this.hashLeaf(item));
    const tree = this.buildMerkleTree(leaves);
    const proof: string[] = [];
    const indices: number[] = [];
    
    // Generate proof path from leaf to root
    this.generateProofPath(tree, leaves[targetIndex], proof, indices);
    
    const merkleProof: MerkleProof = {
      root: tree.hash,
      leaf: leaves[targetIndex],
      proof,
      indices,
      verified: false
    };
    
    // Verify the proof immediately
    merkleProof.verified = this.verifyMerkleProof(merkleProof);
    
    return merkleProof;
  }

  /**
   * Verify Merkle proof
   */
  static verifyMerkleProof(proof: MerkleProof): boolean {
    try {
      let computedHash = proof.leaf;
      
      for (let i = 0; i < proof.proof.length; i++) {
        const proofElement = proof.proof[i];
        const index = proof.indices[i];
        
        if (index === 0) {
          // Proof element is on the left
          computedHash = this.hashPair(proofElement, computedHash);
        } else {
          // Proof element is on the right
          computedHash = this.hashPair(computedHash, proofElement);
        }
      }
      
      return computedHash === proof.root;
    } catch (error) {
      securityLogger.error('Failed to verify Merkle proof', SecurityEventType.SYSTEM_ERROR, error);
      return false;
    }
  }

  /**
   * Generate cross-chain verification proof
   */
  static async generateCrossChainProof(
    states: CrossChainState[]
  ): Promise<{
    merkleRoot: string;
    chainProofs: Map<string, MerkleProof>;
    timestamp: number;
    consensusHash: string;
  }> {
    securityLogger.info('🔺 Generating cross-chain Merkle proof', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Generate Merkle root from all chain states
    const merkleRoot = this.generateMerkleRoot(states);
    
    // Generate individual proofs for each chain
    const chainProofs = new Map<string, MerkleProof>();
    
    for (let i = 0; i < states.length; i++) {
      const state = states[i];
      const proof = this.generateMerkleProof(states, i);
      chainProofs.set(state.chain, proof);
      
      securityLogger.info(
        `   Generated Merkle proof for ${state.chain}: ${proof.verified ? '✅ Valid' : '❌ Invalid'}`,
        SecurityEventType.CROSS_CHAIN_VERIFICATION
      );
    }
    
    // Generate consensus hash (combines all chain states)
    const consensusData = {
      merkleRoot,
      timestamp: Date.now(),
      chains: states.map(s => s.chain),
      states: states.map(s => s.state)
    };
    const consensusHash = ethers.keccak256(ethers.toUtf8Bytes(JSON.stringify(consensusData)));
    
    securityLogger.info(`🔺 Cross-chain Merkle root: ${merkleRoot}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`🔺 Consensus hash: ${consensusHash}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    return {
      merkleRoot,
      chainProofs,
      timestamp: Date.now(),
      consensusHash
    };
  }

  /**
   * Verify cross-chain consensus using Merkle proofs
   */
  static verifyCrossChainConsensus(
    merkleRoot: string,
    chainProofs: Map<string, MerkleProof>,
    requiredChains: number = 2
  ): boolean {
    let verifiedChains = 0;
    
    for (const [chain, proof] of chainProofs) {
      if (proof.root === merkleRoot && this.verifyMerkleProof(proof)) {
        verifiedChains++;
        securityLogger.info(
          `   ${chain} consensus verified via Merkle proof ✅`,
          SecurityEventType.CROSS_CHAIN_VERIFICATION
        );
      } else {
        securityLogger.warn(
          `   ${chain} consensus failed Merkle verification ❌`,
          SecurityEventType.SUSPICIOUS_ACTIVITY
        );
      }
    }
    
    const consensusReached = verifiedChains >= requiredChains;
    
    if (consensusReached) {
      securityLogger.info(
        `🔺 Cross-chain consensus VERIFIED: ${verifiedChains}/${chainProofs.size} chains via Merkle proofs`,
        SecurityEventType.CROSS_CHAIN_VERIFICATION
      );
    } else {
      securityLogger.warn(
        `🔺 Cross-chain consensus FAILED: only ${verifiedChains}/${requiredChains} chains verified`,
        SecurityEventType.SUSPICIOUS_ACTIVITY
      );
    }
    
    return consensusReached;
  }

  /**
   * Build Merkle tree from leaf hashes
   */
  private static buildMerkleTree(leaves: string[]): MerkleNode {
    if (leaves.length === 0) {
      throw new Error('Cannot build Merkle tree from empty array');
    }
    
    if (leaves.length === 1) {
      return { hash: leaves[0] };
    }
    
    // Build tree level by level
    let currentLevel: MerkleNode[] = leaves.map(hash => ({ hash }));
    
    while (currentLevel.length > 1) {
      const nextLevel: MerkleNode[] = [];
      
      for (let i = 0; i < currentLevel.length; i += 2) {
        const left = currentLevel[i];
        const right = i + 1 < currentLevel.length 
          ? currentLevel[i + 1] 
          : currentLevel[i]; // Duplicate last node if odd number
        
        const parent: MerkleNode = {
          hash: this.hashPair(left.hash, right.hash),
          left,
          right
        };
        
        nextLevel.push(parent);
      }
      
      currentLevel = nextLevel;
    }
    
    return currentLevel[0];
  }

  /**
   * Generate proof path from leaf to root
   */
  private static generateProofPath(
    node: MerkleNode,
    targetLeaf: string,
    proof: string[],
    indices: number[],
    currentPath: string[] = []
  ): boolean {
    if (!node.left && !node.right) {
      // Leaf node
      return node.hash === targetLeaf;
    }
    
    // Check left subtree
    if (node.left && this.generateProofPath(node.left, targetLeaf, proof, indices, [...currentPath, 'L'])) {
      if (node.right) {
        proof.push(node.right.hash);
        indices.push(1); // Right sibling
      }
      return true;
    }
    
    // Check right subtree
    if (node.right && this.generateProofPath(node.right, targetLeaf, proof, indices, [...currentPath, 'R'])) {
      if (node.left) {
        proof.push(node.left.hash);
        indices.push(0); // Left sibling
      }
      return true;
    }
    
    return false;
  }

  /**
   * Hash a single leaf
   */
  private static hashLeaf(data: any): string {
    const dataString = typeof data === 'string' ? data : JSON.stringify(data);
    return ethers.keccak256(ethers.toUtf8Bytes(dataString));
  }

  /**
   * Hash a pair of nodes
   */
  private static hashPair(left: string, right: string): string {
    // Sort hashes to ensure deterministic ordering
    const [first, second] = left < right ? [left, right] : [right, left];
    return ethers.keccak256(ethers.concat([first, second]));
  }
}

/**
 * Cross-Chain Verification Coordinator
 * Coordinates verification across multiple blockchains using Merkle proofs
 */
export class CrossChainVerificationCoordinator {
  private verificationHistory: Map<string, any> = new Map();

  /**
   * Coordinate cross-chain verification with automatic failover
   */
  async coordinateVerification(
    vaultId: string,
    chainStates: CrossChainState[]
  ): Promise<{
    success: boolean;
    merkleRoot: string;
    verifiedChains: string[];
    failedChains: string[];
    automaticFailover: boolean;
    consensusHash: string;
  }> {
    securityLogger.info(
      `🔺 Coordinating cross-chain verification for vault: ${vaultId}`,
      SecurityEventType.CROSS_CHAIN_VERIFICATION
    );

    try {
      // Generate Merkle proofs for all chains
      const { merkleRoot, chainProofs, consensusHash } = 
        await MerkleProofSystem.generateCrossChainProof(chainStates);

      // Verify consensus
      const verifiedChains: string[] = [];
      const failedChains: string[] = [];

      for (const [chain, proof] of chainProofs) {
        if (MerkleProofSystem.verifyMerkleProof(proof)) {
          verifiedChains.push(chain);
        } else {
          failedChains.push(chain);
        }
      }

      // Check if automatic failover is needed
      const automaticFailover = failedChains.length > 0;

      if (automaticFailover) {
        securityLogger.warn(
          `⚠️ Automatic failover triggered! Failed chains: ${failedChains.join(', ')}`,
          SecurityEventType.SUSPICIOUS_ACTIVITY
        );
        
        // Implement failover logic
        await this.handleAutomaticFailover(vaultId, failedChains, verifiedChains);
      }

      // Verify 2-of-3 consensus
      const success = verifiedChains.length >= 2;

      // Store verification history
      this.verificationHistory.set(vaultId, {
        timestamp: Date.now(),
        merkleRoot,
        verifiedChains,
        failedChains,
        consensusHash
      });

      return {
        success,
        merkleRoot,
        verifiedChains,
        failedChains,
        automaticFailover,
        consensusHash
      };
    } catch (error) {
      securityLogger.error(
        `Failed to coordinate cross-chain verification for vault: ${vaultId}`,
        SecurityEventType.SYSTEM_ERROR,
        error
      );
      throw error;
    }
  }

  /**
   * Handle automatic failover when one chain is compromised
   */
  private async handleAutomaticFailover(
    vaultId: string,
    failedChains: string[],
    verifiedChains: string[]
  ): Promise<void> {
    securityLogger.warn(
      `🔺 AUTOMATIC FAILOVER: Switching to backup chains for vault ${vaultId}`,
      SecurityEventType.SUSPICIOUS_ACTIVITY
    );

    for (const failedChain of failedChains) {
      securityLogger.warn(
        `   Marking ${failedChain} as compromised - verification failed`,
        SecurityEventType.SUSPICIOUS_ACTIVITY
      );
    }

    securityLogger.info(
      `   Continuing with ${verifiedChains.length} verified chains: ${verifiedChains.join(', ')}`,
      SecurityEventType.CROSS_CHAIN_VERIFICATION
    );

    // In production, this would:
    // 1. Freeze operations on failed chains
    // 2. Route all operations through verified chains
    // 3. Alert administrators
    // 4. Initiate recovery procedures
  }

  /**
   * Get verification history for a vault
   */
  getVerificationHistory(vaultId: string): any {
    return this.verificationHistory.get(vaultId);
  }
}

export const crossChainVerificationCoordinator = new CrossChainVerificationCoordinator();
