/**
 * State Merkle Tree
 * 
 * This module implements Merkle trees for vault state synchronization
 * across multiple blockchains. It enables efficient verification of
 * state consistency without requiring full state data transfer.
 */

import { createHash } from 'crypto';
import { BlockchainType } from '../../shared/types';
import { securityLogger } from '../monitoring/security-logger';

// Define the structure of a state leaf
export interface StateLeaf {
  vaultId: string;
  chain: BlockchainType;
  stateHash: string;
  timestamp: number;
  blockHeight?: number;
  transactionId?: string;
  metadata?: Record<string, any>;
}

// Define the structure of a Merkle node
interface MerkleNode {
  hash: string;
  left?: MerkleNode;
  right?: MerkleNode;
  data?: StateLeaf; // Only leaf nodes have data
}

// Define the structure of a Merkle proof
export interface MerkleProof {
  leaf: StateLeaf;
  proofHashes: string[];
  rootHash: string;
  timestamp: number;
}

// Define the structure of a multi-chain state snapshot
export interface MultiChainStateSnapshot {
  vaultId: string;
  rootHash: string;
  timestamp: number;
  chainStates: Record<BlockchainType, StateLeaf>;
  merkleRoot: MerkleNode;
}

/**
 * State Merkle Tree Service
 * 
 * Implements Merkle trees for efficient cross-chain state verification
 */
class StateMerkleTreeService {
  private vaultStateSnapshots: Map<string, MultiChainStateSnapshot> = new Map();
  
  constructor() {
    securityLogger.info('State Merkle Tree service initialized');
  }
  
  /**
   * Create a hash from state data
   */
  private createStateHash(state: any): string {
    const stateStr = typeof state === 'string' ? state : JSON.stringify(state);
    return createHash('sha256').update(stateStr).digest('hex');
  }
  
  /**
   * Create a Merkle leaf from state data
   */
  createStateLeaf(
    vaultId: string,
    chain: BlockchainType,
    state: any,
    timestamp: number,
    blockHeight?: number,
    transactionId?: string,
    metadata?: Record<string, any>
  ): StateLeaf {
    const stateHash = this.createStateHash(state);
    
    return {
      vaultId,
      chain,
      stateHash,
      timestamp,
      blockHeight,
      transactionId,
      metadata
    };
  }
  
  /**
   * Create a Merkle tree from a list of state leaves
   */
  private buildMerkleTree(leaves: StateLeaf[]): MerkleNode {
    if (leaves.length === 0) {
      throw new Error('Cannot build Merkle tree with no leaves');
    }
    
    // Create leaf nodes
    let nodes: MerkleNode[] = leaves.map(leaf => ({
      hash: this.createStateHash(leaf),
      data: leaf
    }));
    
    // Build tree bottom-up
    while (nodes.length > 1) {
      const nextLevel: MerkleNode[] = [];
      
      for (let i = 0; i < nodes.length; i += 2) {
        if (i + 1 < nodes.length) {
          // Create a parent node with two children
          const left = nodes[i];
          const right = nodes[i + 1];
          const combinedHash = this.createStateHash(left.hash + right.hash);
          
          nextLevel.push({
            hash: combinedHash,
            left,
            right
          });
        } else {
          // Odd number of nodes, promote the last one
          nextLevel.push(nodes[i]);
        }
      }
      
      nodes = nextLevel;
    }
    
    return nodes[0]; // Root node
  }
  
  /**
   * Create or update a multi-chain state snapshot for a vault
   */
  updateVaultStateSnapshot(
    vaultId: string,
    chainStates: Record<BlockchainType, StateLeaf>
  ): MultiChainStateSnapshot {
    // Convert the state map to an array of leaves
    const stateLeaves = Object.values(chainStates);
    
    // Build the Merkle tree
    const merkleRoot = this.buildMerkleTree(stateLeaves);
    
    // Create the snapshot
    const snapshot: MultiChainStateSnapshot = {
      vaultId,
      rootHash: merkleRoot.hash,
      timestamp: Date.now(),
      chainStates,
      merkleRoot
    };
    
    // Store the snapshot
    this.vaultStateSnapshots.set(vaultId, snapshot);
    
    securityLogger.info(`Updated state Merkle tree for vault ${vaultId}`, {
      vaultId,
      rootHash: merkleRoot.hash,
      chains: Object.keys(chainStates),
      timestamp: snapshot.timestamp
    });
    
    return snapshot;
  }
  
  /**
   * Get a vault's state snapshot
   */
  getVaultStateSnapshot(vaultId: string): MultiChainStateSnapshot | undefined {
    return this.vaultStateSnapshots.get(vaultId);
  }
  
  /**
   * Generate a Merkle proof for a specific chain's state
   */
  generateStateProof(vaultId: string, chain: BlockchainType): MerkleProof | null {
    const snapshot = this.vaultStateSnapshots.get(vaultId);
    
    if (!snapshot || !snapshot.chainStates[chain]) {
      return null;
    }
    
    const leaf = snapshot.chainStates[chain];
    const proofHashes: string[] = this.generateMerkleProof(snapshot.merkleRoot, leaf);
    
    return {
      leaf,
      proofHashes,
      rootHash: snapshot.rootHash,
      timestamp: Date.now()
    };
  }
  
  /**
   * Generate the Merkle proof hashes for a leaf
   */
  private generateMerkleProof(root: MerkleNode, targetLeaf: StateLeaf): string[] {
    const proofHashes: string[] = [];
    
    // Recursively search for the leaf and build the proof
    const findLeaf = (node: MerkleNode, proof: string[]): boolean => {
      // If this is a leaf node
      if (node.data) {
        // Check if this is the target leaf
        return node.data.vaultId === targetLeaf.vaultId && 
               node.data.chain === targetLeaf.chain &&
               node.data.stateHash === targetLeaf.stateHash;
      }
      
      // Not a leaf, check left subtree
      if (node.left && findLeaf(node.left, proof)) {
        // The leaf was found in the left subtree, add right hash to proof
        if (node.right) {
          proof.push(node.right.hash);
        }
        return true;
      }
      
      // Check right subtree
      if (node.right && findLeaf(node.right, proof)) {
        // The leaf was found in the right subtree, add left hash to proof
        if (node.left) {
          proof.push(node.left.hash);
        }
        return true;
      }
      
      // Leaf not found in this subtree
      return false;
    };
    
    findLeaf(root, proofHashes);
    return proofHashes;
  }
  
  /**
   * Verify a Merkle proof
   */
  verifyStateProof(proof: MerkleProof): boolean {
    let computedHash = this.createStateHash(proof.leaf);
    
    // Combine with each proof hash to compute the root
    for (const proofHash of proof.proofHashes) {
      computedHash = this.createStateHash(computedHash + proofHash);
    }
    
    // Verify the computed hash matches the root hash
    return computedHash === proof.rootHash;
  }
}

// Export a singleton instance
export const stateMerkleTreeService = new StateMerkleTreeService();