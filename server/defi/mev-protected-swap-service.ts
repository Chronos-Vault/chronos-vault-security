/**
 * MEV-Protected Atomic Swap Service
 * 
 * Wraps existing Atomic Swap Service with MEV protection layer:
 * 1. Commit phase: User commits to swap parameters
 * 2. Reveal phase: After delay, user reveals parameters
 * 3. Execute phase: Swap executes via private mempool (Flashbots)
 * 
 * Prevents front-running, sandwich attacks, and other MEV exploits
 */

import { AtomicSwapService, AtomicSwapOrder } from './atomic-swap-service';
import { mevProtection, CommitParams, MEVProtectedTransaction } from '../security/mev-protection';
import { anomalyDetector, OperationMetrics } from '../security/anomaly-detector';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';
import crypto from 'crypto';

export interface MEVProtectedSwapRequest {
  userAddress: string;
  fromToken: string;
  toToken: string;
  amount: string;
  minOutput: string;
  fromChain: string;
  toChain: string;
}

export interface MEVProtectedSwapResult {
  commitmentId: string;
  status: 'committed' | 'revealed' | 'executed';
  revealDeadline?: number;
  executionDeadline?: number;
  txHash?: string;
  estimatedOutput?: string;
}

export class MEVProtectedSwapService {
  private atomicSwapService: AtomicSwapService;
  private pendingSwaps: Map<string, MEVProtectedSwapRequest> = new Map();
  private commitNonces: Map<string, string> = new Map(); // Store nonces for reveal phase

  constructor() {
    this.atomicSwapService = new AtomicSwapService();
    
    securityLogger.info('🛡️ MEV-Protected Swap Service initialized', SecurityEventType.SYSTEM_ERROR);
    securityLogger.info('   Protection: Commit-reveal + Private mempool', SecurityEventType.SYSTEM_ERROR);
  }

  /**
   * Step 1: COMMIT to swap parameters
   * User commits hash of parameters without revealing details
   */
  async commitSwap(request: MEVProtectedSwapRequest): Promise<MEVProtectedSwapResult> {
    securityLogger.info(`🔒 MEV Protection: Committing swap`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   User: ${request.userAddress}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   ${request.fromToken} → ${request.toToken}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Generate nonce for uniqueness
    const nonce = crypto.randomBytes(32).toString('hex');
    
    // Create commitment parameters
    const commitParams: CommitParams = {
      userAddress: request.userAddress,
      fromToken: request.fromToken,
      toToken: request.toToken,
      amount: request.amount,
      minOutput: request.minOutput,
      fromChain: request.fromChain,
      toChain: request.toChain,
      nonce
    };
    
    // Commit transaction
    const commitmentId = await mevProtection.commitTransaction(commitParams);
    
    // Store swap request AND nonce for later reveal
    this.pendingSwaps.set(commitmentId, request);
    this.commitNonces.set(commitmentId, nonce);
    
    // Get commitment status
    const commitment = mevProtection.getCommitmentStatus(commitmentId);
    
    if (!commitment) {
      throw new Error('Failed to create commitment');
    }
    
    return {
      commitmentId,
      status: 'committed',
      revealDeadline: commitment.revealDeadline,
      executionDeadline: commitment.executionDeadline
    };
  }

  /**
   * Step 2: REVEAL swap parameters
   * After commit delay, reveal actual swap details
   */
  async revealSwap(commitmentId: string): Promise<MEVProtectedSwapResult> {
    const request = this.pendingSwaps.get(commitmentId);
    
    if (!request) {
      throw new Error('Commitment not found');
    }
    
    securityLogger.info(`🔓 MEV Protection: Revealing swap`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Commitment: ${commitmentId}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Retrieve stored nonce from commit phase
    const nonce = this.commitNonces.get(commitmentId);
    if (!nonce) {
      throw new Error('Nonce not found - commitment may have expired');
    }
    
    const commitParams: CommitParams = {
      userAddress: request.userAddress,
      fromToken: request.fromToken,
      toToken: request.toToken,
      amount: request.amount,
      minOutput: request.minOutput,
      fromChain: request.fromChain,
      toChain: request.toChain,
      nonce
    };
    
    // Reveal transaction
    await mevProtection.revealTransaction(commitmentId, commitParams);
    
    // Get optimal route (now that parameters are revealed)
    const routes = await this.atomicSwapService.findOptimalRoute(
      request.fromToken,
      request.toToken,
      request.amount,
      request.fromChain as any,
      request.toChain as any
    );
    
    const estimatedOutput = routes[0]?.estimatedOutput || '0';
    
    return {
      commitmentId,
      status: 'revealed',
      estimatedOutput
    };
  }

  /**
   * Step 3: EXECUTE swap via MEV protection
   * Executes through Flashbots private mempool if available
   */
  async executeProtectedSwap(commitmentId: string): Promise<MEVProtectedSwapResult> {
    const request = this.pendingSwaps.get(commitmentId);
    
    if (!request) {
      throw new Error('Commitment not found');
    }
    
    securityLogger.info(`⚡ MEV Protection: Executing swap`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Commitment: ${commitmentId}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Execute MEV-protected transaction
    const txHash = await mevProtection.executeProtectedTransaction(commitmentId);
    
    // Create atomic swap order using service
    const swapOrder = await this.atomicSwapService.createAtomicSwap(
      request.userAddress,
      request.fromToken,
      request.toToken,
      request.amount,
      request.minOutput,
      request.fromChain as any,
      request.toChain as any
    );
    
    // Lock the swap order
    await this.atomicSwapService.lockSwapFunds(swapOrder.id, swapOrder.secretHash);
    
    // Execute actual swap
    const swapTxHash = await this.atomicSwapService.executeAtomicSwap(swapOrder.id);
    
    // Track with anomaly detector
    const metrics: OperationMetrics = {
      operationId: commitmentId,
      type: 'swap',
      amount: parseFloat(request.amount),
      timestamp: new Date(),
      chainFrom: request.fromChain,
      chainTo: request.toChain,
      success: true
    };
    
    await anomalyDetector.processOperation(metrics);
    
    // Cleanup
    this.pendingSwaps.delete(commitmentId);
    this.commitNonces.delete(commitmentId);
    
    securityLogger.info(`✅ MEV-Protected swap executed successfully`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.info(`   Transaction: ${swapTxHash}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    return {
      commitmentId,
      status: 'executed',
      txHash: swapTxHash
    };
  }

  /**
   * Full MEV-protected swap (all steps combined)
   * For simplified usage
   */
  async executeFullProtectedSwap(request: MEVProtectedSwapRequest): Promise<MEVProtectedSwapResult> {
    securityLogger.info('🛡️ Starting full MEV-protected swap flow', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Step 1: Commit
    const commitResult = await this.commitSwap(request);
    const commitmentId = commitResult.commitmentId;
    
    // Step 2: Wait for commit delay (simulated - in production, user waits)
    securityLogger.info('⏳ Waiting for commit delay...', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    await new Promise(resolve => setTimeout(resolve, 15000)); // 15 seconds
    
    // Step 3: Reveal
    const revealResult = await this.revealSwap(commitmentId);
    
    // Step 4: Execute
    const executeResult = await this.executeProtectedSwap(commitmentId);
    
    return executeResult;
  }

  /**
   * Get commitment status
   */
  getCommitmentStatus(commitmentId: string): MEVProtectedTransaction | null {
    return mevProtection.getCommitmentStatus(commitmentId);
  }

  /**
   * Get MEV protection statistics
   */
  getMEVStats() {
    return mevProtection.getStatistics();
  }

  /**
   * Get anomaly detection metrics
   */
  getAnomalyMetrics() {
    return anomalyDetector.getMetrics();
  }
}

// Singleton instance
export const mevProtectedSwapService = new MEVProtectedSwapService();
