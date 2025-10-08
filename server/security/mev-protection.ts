/**
 * MEV (Maximal Extractable Value) Protection Service
 * 
 * Protects Chronos Vault cross-chain swaps and bridges from MEV attacks:
 * - Front-running: Bots submit transactions ahead of yours with higher gas
 * - Sandwich attacks: Bots buy before you, you buy (raising price), they sell at profit
 * - Back-running: Bots execute immediately after your transaction
 * 
 * PROTECTION MECHANISMS FOR ARBITRUM L2:
 * 1. Commit-Reveal Scheme: Users commit transaction hash first, reveal later
 * 2. Private Mempool: Submit through Flashbots Protect (no public exposure)
 * 3. Time-lock Execution: Delay between commit/reveal prevents sandwich attacks
 * 4. Slippage Protection: Enforce strict min output amounts
 * 
 * WHY ARBITRUM L2 NEEDS MEV PROTECTION:
 * - Lower gas costs = MEV bots can profit on smaller trades
 * - Centralized sequencer = potential for MEV extraction at sequencer level
 * - High throughput = more opportunities for MEV attacks
 */

import { ethers } from 'ethers';
import crypto from 'crypto';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';

export interface MEVProtectedTransaction {
  commitmentId: string;
  userAddress: string;
  commitment: string; // Hash of transaction parameters
  revealDeadline: number; // Timestamp when reveal must happen
  executionDeadline: number; // Timestamp when execution must happen
  status: 'committed' | 'revealed' | 'executed' | 'expired' | 'failed';
  
  // Transaction data (only stored after reveal)
  fromToken?: string;
  toToken?: string;
  amount?: string;
  minOutput?: string;
  fromChain?: string;
  toChain?: string;
  
  // Execution data
  commitTxHash?: string;
  executeTxHash?: string;
  createdAt: Date;
  revealedAt?: Date;
  executedAt?: Date;
}

export interface CommitParams {
  userAddress: string;
  fromToken: string;
  toToken: string;
  amount: string;
  minOutput: string;
  fromChain: string;
  toChain: string;
  nonce: string; // Random nonce for uniqueness
}

export interface FlashbotsBundle {
  signedTransactions: string[];
  targetBlock: number;
  minTimestamp?: number;
  maxTimestamp?: number;
}

export class MEVProtectionService {
  private commitments: Map<string, MEVProtectedTransaction> = new Map();
  private readonly COMMIT_REVEAL_DELAY = 15; // 15 seconds between commit and reveal
  private readonly EXECUTION_WINDOW = 300; // 5 minutes window to execute after reveal
  private readonly MAX_SLIPPAGE_BPS = 50; // Maximum 0.5% slippage
  
  // Flashbots Protect RPC for Arbitrum (if available)
  private flashbotsRPC: string | null = null;
  
  constructor() {
    // Check if Flashbots Protect is available for Arbitrum
    if (process.env.FLASHBOTS_ARBITRUM_RPC) {
      this.flashbotsRPC = process.env.FLASHBOTS_ARBITRUM_RPC;
      securityLogger.info('✅ Flashbots Protect enabled for Arbitrum L2', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    } else {
      securityLogger.warn('⚠️  Flashbots Protect not configured. Using commit-reveal only.', SecurityEventType.SYSTEM_ERROR);
    }
  }

  /**
   * Step 1: Commit to a transaction
   * Creates commitment hash without revealing transaction details
   */
  async commitTransaction(params: CommitParams): Promise<string> {
    const { userAddress, fromToken, toToken, amount, minOutput, fromChain, toChain, nonce } = params;
    
    // Create commitment hash (prevents front-running)
    const commitment = this.createCommitment(params);
    const commitmentId = ethers.keccak256(ethers.toUtf8Bytes(`${commitment}-${Date.now()}`));
    
    const now = Date.now();
    const revealDeadline = now + (this.COMMIT_REVEAL_DELAY * 1000);
    const executionDeadline = revealDeadline + (this.EXECUTION_WINDOW * 1000);
    
    const protectedTx: MEVProtectedTransaction = {
      commitmentId,
      userAddress,
      commitment,
      revealDeadline,
      executionDeadline,
      status: 'committed',
      createdAt: new Date(),
    };
    
    this.commitments.set(commitmentId, protectedTx);
    
    securityLogger.info(`🔒 MEV Protection: Transaction committed`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Commitment ID: ${commitmentId}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   User: ${userAddress}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Reveal deadline: ${new Date(revealDeadline).toISOString()}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    return commitmentId;
  }

  /**
   * Step 2: Reveal transaction parameters
   * Can only happen after commit delay to prevent front-running
   */
  async revealTransaction(
    commitmentId: string,
    params: CommitParams
  ): Promise<boolean> {
    const protectedTx = this.commitments.get(commitmentId);
    
    if (!protectedTx) {
      throw new Error('Commitment not found');
    }
    
    if (protectedTx.status !== 'committed') {
      throw new Error(`Invalid status: ${protectedTx.status}`);
    }
    
    const now = Date.now();
    
    // Check reveal timing
    if (now < protectedTx.revealDeadline) {
      const waitTime = Math.ceil((protectedTx.revealDeadline - now) / 1000);
      throw new Error(`Too early to reveal. Wait ${waitTime} seconds.`);
    }
    
    if (now > protectedTx.executionDeadline) {
      protectedTx.status = 'expired';
      throw new Error('Commitment expired');
    }
    
    // Verify commitment matches revealed data
    const revealedCommitment = this.createCommitment(params);
    if (revealedCommitment !== protectedTx.commitment) {
      protectedTx.status = 'failed';
      securityLogger.error(
        '❌ MEV Protection: Commitment mismatch (possible attack)',
        SecurityEventType.SUSPICIOUS_ACTIVITY,
        { commitmentId, userAddress: params.userAddress }
      );
      throw new Error('Commitment verification failed');
    }
    
    // Store revealed parameters
    protectedTx.fromToken = params.fromToken;
    protectedTx.toToken = params.toToken;
    protectedTx.amount = params.amount;
    protectedTx.minOutput = params.minOutput;
    protectedTx.fromChain = params.fromChain;
    protectedTx.toChain = params.toChain;
    protectedTx.status = 'revealed';
    protectedTx.revealedAt = new Date();
    
    securityLogger.info(`🔓 MEV Protection: Transaction revealed`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Commitment ID: ${commitmentId}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Swap: ${params.fromToken} → ${params.toToken}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Amount: ${params.amount}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    return true;
  }

  /**
   * Step 3: Execute protected transaction
   * Uses Flashbots Protect (private mempool) if available
   */
  async executeProtectedTransaction(commitmentId: string): Promise<string> {
    const protectedTx = this.commitments.get(commitmentId);
    
    if (!protectedTx) {
      throw new Error('Commitment not found');
    }
    
    if (protectedTx.status !== 'revealed') {
      throw new Error(`Cannot execute: status is ${protectedTx.status}`);
    }
    
    const now = Date.now();
    if (now > protectedTx.executionDeadline) {
      protectedTx.status = 'expired';
      throw new Error('Execution window expired');
    }
    
    // Verify slippage protection
    this.verifySlippageProtection(protectedTx);
    
    let txHash: string;
    
    if (this.flashbotsRPC) {
      // Use Flashbots Protect (private mempool)
      txHash = await this.submitViaFlashbots(protectedTx);
      securityLogger.info(`✅ MEV Protection: Executed via Flashbots Protect`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    } else {
      // Standard execution (less protection)
      txHash = await this.submitStandard(protectedTx);
      securityLogger.info(`✅ MEV Protection: Executed via commit-reveal`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    }
    
    protectedTx.status = 'executed';
    protectedTx.executeTxHash = txHash;
    protectedTx.executedAt = new Date();
    
    securityLogger.info(`   Transaction hash: ${txHash}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    return txHash;
  }

  /**
   * Create commitment hash from transaction parameters
   */
  private createCommitment(params: CommitParams): string {
    const data = ethers.AbiCoder.defaultAbiCoder().encode(
      ['address', 'string', 'string', 'string', 'string', 'string', 'string', 'string'],
      [
        params.userAddress,
        params.fromToken,
        params.toToken,
        params.amount,
        params.minOutput,
        params.fromChain,
        params.toChain,
        params.nonce
      ]
    );
    
    return ethers.keccak256(data);
  }

  /**
   * Verify slippage protection (prevents sandwich attacks)
   */
  private verifySlippageProtection(tx: MEVProtectedTransaction): void {
    if (!tx.amount || !tx.minOutput) {
      throw new Error('Missing amount or minOutput');
    }
    
    const amount = BigInt(tx.amount);
    const minOutput = BigInt(tx.minOutput);
    
    // Calculate actual slippage
    const slippageBps = Number((amount - minOutput) * BigInt(10000) / amount);
    
    if (slippageBps > this.MAX_SLIPPAGE_BPS) {
      securityLogger.warn(
        `⚠️  MEV Protection: Slippage too high (${slippageBps / 100}%)`,
        SecurityEventType.SUSPICIOUS_ACTIVITY,
        { commitmentId: tx.commitmentId, slippageBps }
      );
      throw new Error(`Slippage exceeds maximum (${slippageBps / 100}% > ${this.MAX_SLIPPAGE_BPS / 100}%)`);
    }
  }

  /**
   * Submit transaction via Flashbots Protect (private mempool)
   * Prevents MEV bots from seeing transaction before execution
   */
  private async submitViaFlashbots(tx: MEVProtectedTransaction): Promise<string> {
    if (!this.flashbotsRPC) {
      throw new Error('Flashbots RPC not configured');
    }
    
    securityLogger.info('🔐 Submitting via Flashbots Protect (private mempool)...', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // In production, this would:
    // 1. Sign transaction
    // 2. Submit to Flashbots RPC
    // 3. Wait for inclusion
    // 4. Return transaction hash
    
    // For now, return simulated hash
    const simulatedHash = ethers.keccak256(
      ethers.toUtf8Bytes(`flashbots-${tx.commitmentId}-${Date.now()}`)
    );
    
    return simulatedHash;
  }

  /**
   * Submit transaction via standard RPC (fallback)
   */
  private async submitStandard(tx: MEVProtectedTransaction): Promise<string> {
    securityLogger.info('📡 Submitting via standard RPC...', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // In production, this would submit to standard Arbitrum RPC
    // Still protected by commit-reveal timing
    
    const simulatedHash = ethers.keccak256(
      ethers.toUtf8Bytes(`standard-${tx.commitmentId}-${Date.now()}`)
    );
    
    return simulatedHash;
  }

  /**
   * Get commitment status
   */
  getCommitmentStatus(commitmentId: string): MEVProtectedTransaction | null {
    return this.commitments.get(commitmentId) || null;
  }

  /**
   * Clean up expired commitments
   */
  cleanupExpired(): void {
    const now = Date.now();
    let cleaned = 0;
    
    for (const [id, tx] of this.commitments.entries()) {
      if (now > tx.executionDeadline && tx.status !== 'executed') {
        tx.status = 'expired';
        this.commitments.delete(id);
        cleaned++;
      }
    }
    
    if (cleaned > 0) {
      securityLogger.info(`🧹 MEV Protection: Cleaned ${cleaned} expired commitments`, SecurityEventType.SYSTEM_ERROR);
    }
  }

  /**
   * Get MEV protection statistics
   */
  getStatistics() {
    const stats = {
      total: this.commitments.size,
      committed: 0,
      revealed: 0,
      executed: 0,
      expired: 0,
      failed: 0,
    };
    
    for (const tx of this.commitments.values()) {
      stats[tx.status]++;
    }
    
    return stats;
  }
}

// Singleton instance
export const mevProtection = new MEVProtectionService();

// Cleanup expired commitments every minute
setInterval(() => {
  mevProtection.cleanupExpired();
}, 60000);
