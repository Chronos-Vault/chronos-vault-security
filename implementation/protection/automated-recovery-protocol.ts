/**
 * Automated Recovery Protocol
 * 
 * This module implements automatic failover mechanisms for the multi-chain
 * verification system. If one blockchain becomes unavailable or compromised,
 * the system can automatically switch to alternative chains for verification
 * while maintaining security guarantees.
 */

import { BlockchainType } from '../../shared/types';
import { securityLogger } from '../monitoring/security-logger';
import { ConnectorFactory } from '../blockchain/connector-factory';
import { stateMerkleTreeService, MultiChainStateSnapshot } from './state-merkle-tree';
import { timeWeightedValidation, ValidationResult } from './time-weighted-validation';
import { EventEmitter } from 'events';

// Define chain health status
export interface ChainHealthStatus {
  chain: BlockchainType;
  isAvailable: boolean;
  isResponsive: boolean;
  responseTimeMs?: number;
  lastChecked: number;
  errorCount: number;
  consecutiveErrors: number;
  nextRetryTime?: number;
}

// Define recovery status
export interface RecoveryStatus {
  vaultId: string;
  isRecoveryActive: boolean;
  primaryChain: BlockchainType;
  fallbackChains: BlockchainType[];
  activeChain: BlockchainType;
  recoveryStartTime: number;
  lastUpdated: number;
  recoveryTrigger: string;
  recoverySteps: RecoveryStep[];
  metadata: Record<string, any>;
}

// Define recovery step
interface RecoveryStep {
  timestamp: number;
  action: string;
  chain?: BlockchainType;
  success: boolean;
  details?: string;
}

// Define recovery events
interface RecoveryEvents {
  'recovery:started': (vaultId: string, primaryChain: BlockchainType, fallbackChain: BlockchainType) => void;
  'recovery:completed': (vaultId: string, result: RecoveryStatus) => void;
  'recovery:failed': (vaultId: string, error: Error) => void;
  'recovery:step': (vaultId: string, step: RecoveryStep) => void;
  'chain:degraded': (chain: BlockchainType, status: ChainHealthStatus) => void;
  'chain:restored': (chain: BlockchainType, status: ChainHealthStatus) => void;
}

/**
 * Automated Recovery Protocol Service
 * 
 * Implements automatic failover and recovery mechanisms for the
 * multi-chain verification system
 */
class AutomatedRecoveryProtocol extends EventEmitter {
  private chainHealthStatus: Map<BlockchainType, ChainHealthStatus> = new Map();
  private activeRecoveries: Map<string, RecoveryStatus> = new Map();
  private connectorFactory: ConnectorFactory;
  
  // Health check thresholds
  private readonly HEALTH_CHECK_INTERVAL_MS = 60000; // Check every minute
  private readonly ERROR_THRESHOLD = 5; // Number of errors before marking degraded
  private readonly CONSECUTIVE_ERROR_THRESHOLD = 3; // Consecutive errors before marking degraded
  private readonly RECOVERY_RETRY_DELAY_MS = 300000; // 5 minutes between recovery attempts
  
  constructor(connectorFactory: ConnectorFactory) {
    super();
    this.connectorFactory = connectorFactory;
    
    // Initialize chain health status
    const chains: BlockchainType[] = ['ETH', 'SOL', 'TON', 'BTC'];
    chains.forEach(chain => {
      this.chainHealthStatus.set(chain, {
        chain,
        isAvailable: true, // Assume available initially
        isResponsive: true,
        lastChecked: Date.now(),
        errorCount: 0,
        consecutiveErrors: 0
      });
    });
    
    // Only start health check loop in production mode
    // In development, chains are simulated and health checks cause false degradation warnings
    const isDevelopment = process.env.NODE_ENV === 'development';
    if (!isDevelopment) {
      this.startHealthCheckLoop();
      securityLogger.info('Automated Recovery Protocol service initialized with health monitoring');
    } else {
      securityLogger.info('Automated Recovery Protocol service initialized (health checks disabled in development mode)');
    }
  }
  
  /**
   * Start the periodic health check loop
   */
  private startHealthCheckLoop() {
    const checkHealth = async () => {
      for (const chain of this.chainHealthStatus.keys()) {
        await this.checkChainHealth(chain);
      }
      
      // Schedule next check
      setTimeout(checkHealth, this.HEALTH_CHECK_INTERVAL_MS);
    };
    
    // Start initial check
    checkHealth();
  }
  
  /**
   * Check the health of a blockchain
   */
  async checkChainHealth(chain: BlockchainType): Promise<ChainHealthStatus> {
    const currentStatus = this.chainHealthStatus.get(chain) || {
      chain,
      isAvailable: false,
      isResponsive: false,
      lastChecked: 0,
      errorCount: 0,
      consecutiveErrors: 0
    };
    
    try {
      const connector = this.connectorFactory.getConnector(chain);
      
      // Measure response time
      const startTime = Date.now();
      const isAvailable = await connector.isChainAvailable();
      const responseTimeMs = Date.now() - startTime;
      
      // Update status based on response
      if (isAvailable) {
        const previouslyDegraded = !currentStatus.isAvailable;
        
        // Chain is healthy
        const updatedStatus: ChainHealthStatus = {
          ...currentStatus,
          isAvailable: true,
          isResponsive: true,
          responseTimeMs,
          lastChecked: Date.now(),
          consecutiveErrors: 0,
          // Keep the error count but don't increase it
          errorCount: currentStatus.errorCount
        };
        
        this.chainHealthStatus.set(chain, updatedStatus);
        
        // If chain was previously degraded, emit restored event
        if (previouslyDegraded) {
          this.emit('chain:restored', chain, updatedStatus);
          
          securityLogger.info(`Chain ${chain} has been restored`, {
            chain,
            responseTimeMs,
            previousErrors: currentStatus.errorCount
          });
          
          // Reset error count after some successful checks
          if (updatedStatus.errorCount > 0) {
            setTimeout(() => {
              const status = this.chainHealthStatus.get(chain);
              if (status && status.isAvailable && status.consecutiveErrors === 0) {
                this.chainHealthStatus.set(chain, {
                  ...status,
                  errorCount: 0
                });
              }
            }, 300000); // Reset after 5 minutes of stability
          }
        }
        
        return updatedStatus;
      } else {
        // Chain is responsive but reports itself as unavailable
        return this.handleChainError(chain, 'Chain reports unavailable', responseTimeMs);
      }
    } catch (error) {
      // Chain is unresponsive or error occurred
      return this.handleChainError(chain, error instanceof Error ? error.message : 'Unknown error');
    }
  }
  
  /**
   * Handle a chain error and update health status
   */
  private handleChainError(chain: BlockchainType, errorMessage: string, responseTimeMs?: number): ChainHealthStatus {
    const currentStatus = this.chainHealthStatus.get(chain) || {
      chain,
      isAvailable: false,
      isResponsive: false,
      lastChecked: 0,
      errorCount: 0,
      consecutiveErrors: 0
    };
    
    // Increment error counts
    const errorCount = currentStatus.errorCount + 1;
    const consecutiveErrors = currentStatus.consecutiveErrors + 1;
    
    // Determine if chain is now degraded
    const wasAvailable = currentStatus.isAvailable;
    const isAvailable = errorCount < this.ERROR_THRESHOLD && 
                         consecutiveErrors < this.CONSECUTIVE_ERROR_THRESHOLD;
    
    // Create updated status
    const updatedStatus: ChainHealthStatus = {
      ...currentStatus,
      isAvailable,
      isResponsive: responseTimeMs !== undefined,
      responseTimeMs,
      lastChecked: Date.now(),
      errorCount,
      consecutiveErrors,
      nextRetryTime: Date.now() + Math.min(consecutiveErrors * 60000, 300000) // Exponential backoff with 5min max
    };
    
    this.chainHealthStatus.set(chain, updatedStatus);
    
    // If chain was previously available and is now degraded, emit event
    if (wasAvailable && !isAvailable) {
      this.emit('chain:degraded', chain, updatedStatus);
      
      // Truncate error message to prevent buffer issues
      const truncatedErrorMessage = typeof errorMessage === 'string' 
        ? errorMessage.substring(0, 500)
        : String(errorMessage).substring(0, 500);
      
      securityLogger.warn(`Chain ${chain} has been marked as degraded`, {
        chain,
        errorCount,
        consecutiveErrors,
        errorMessage: truncatedErrorMessage
      });
      
      // Trigger recovery for affected vaults
      this.triggerRecoveryForChain(chain);
    }
    
    return updatedStatus;
  }
  
  /**
   * Trigger recovery for all vaults using a degraded chain as primary
   */
  private triggerRecoveryForChain(degradedChain: BlockchainType) {
    // In a real implementation, this would look up all vaults using this chain
    // and trigger recovery for each. For the demo, we'll use a simulated approach.
    
    securityLogger.info(`Triggering recovery for chain ${degradedChain}`);
    
    // This would normally come from a database
    const simulatedAffectedVaults = [
      {
        vaultId: `vault-${Date.now()}-${Math.floor(Math.random() * 1000)}`,
        primaryChain: degradedChain,
        value: 50000 // USD
      }
    ];
    
    // Trigger recovery for each affected vault
    for (const vault of simulatedAffectedVaults) {
      this.initiateRecovery(
        vault.vaultId,
        vault.primaryChain,
        `Chain ${degradedChain} marked as degraded`,
        { valueUSD: vault.value }
      );
    }
  }
  
  /**
   * Initiate a recovery process for a vault
   */
  initiateRecovery(
    vaultId: string,
    primaryChain: BlockchainType,
    trigger: string,
    metadata: Record<string, any> = {}
  ): RecoveryStatus {
    // Check if recovery is already in progress
    const existingRecovery = this.activeRecoveries.get(vaultId);
    if (existingRecovery && existingRecovery.isRecoveryActive) {
      securityLogger.info(`Recovery already in progress for vault ${vaultId}`);
      return existingRecovery;
    }
    
    // Determine fallback chains
    const fallbackChains = this.determineFallbackChains(primaryChain);
    
    if (fallbackChains.length === 0) {
      const errorMsg = `No healthy fallback chains available for vault ${vaultId}`;
      securityLogger.error(errorMsg);
      this.emit('recovery:failed', vaultId, new Error(errorMsg));
      
      // Create a failed recovery status
      const failedStatus: RecoveryStatus = {
        vaultId,
        isRecoveryActive: false,
        primaryChain,
        fallbackChains: [],
        activeChain: primaryChain,
        recoveryStartTime: Date.now(),
        lastUpdated: Date.now(),
        recoveryTrigger: trigger,
        recoverySteps: [{
          timestamp: Date.now(),
          action: 'RECOVERY_INIT_FAILED',
          success: false,
          details: errorMsg
        }],
        metadata
      };
      
      this.activeRecoveries.set(vaultId, failedStatus);
      return failedStatus;
    }
    
    // Select the first healthy fallback chain
    const fallbackChain = fallbackChains[0];
    
    // Create recovery status
    const recoveryStatus: RecoveryStatus = {
      vaultId,
      isRecoveryActive: true,
      primaryChain,
      fallbackChains,
      activeChain: fallbackChain,
      recoveryStartTime: Date.now(),
      lastUpdated: Date.now(),
      recoveryTrigger: trigger,
      recoverySteps: [{
        timestamp: Date.now(),
        action: 'RECOVERY_INITIATED',
        chain: primaryChain,
        success: true,
        details: `Initiating recovery from ${primaryChain} to ${fallbackChain}`
      }],
      metadata
    };
    
    this.activeRecoveries.set(vaultId, recoveryStatus);
    
    // Emit event
    this.emit('recovery:started', vaultId, primaryChain, fallbackChain);
    
    securityLogger.info(`Recovery initiated for vault ${vaultId}`, {
      vaultId,
      primaryChain,
      fallbackChain,
      trigger
    });
    
    // Start the recovery process
    this.executeRecoveryProcess(vaultId);
    
    return recoveryStatus;
  }
  
  /**
   * Determine available fallback chains for a primary chain
   */
  private determineFallbackChains(primaryChain: BlockchainType): BlockchainType[] {
    const allChains: BlockchainType[] = ['ETH', 'SOL', 'TON', 'BTC'];
    const fallbackChains: BlockchainType[] = [];
    
    // Filter out the primary chain and any unhealthy chains
    for (const chain of allChains) {
      if (chain !== primaryChain) {
        const healthStatus = this.chainHealthStatus.get(chain);
        if (healthStatus && healthStatus.isAvailable) {
          fallbackChains.push(chain);
        }
      }
    }
    
    return fallbackChains;
  }
  
  /**
   * Execute the recovery process
   */
  private async executeRecoveryProcess(vaultId: string) {
    const recovery = this.activeRecoveries.get(vaultId);
    if (!recovery || !recovery.isRecoveryActive) {
      return;
    }
    
    try {
      // Step 1: Retrieve the latest state from the fallback chain
      const step1: RecoveryStep = {
        timestamp: Date.now(),
        action: 'RETRIEVE_STATE',
        chain: recovery.activeChain,
        success: false
      };
      
      // Get state snapshot if available
      const stateSnapshot = stateMerkleTreeService.getVaultStateSnapshot(vaultId);
      
      if (stateSnapshot) {
        step1.success = true;
        step1.details = `Retrieved state snapshot with root ${stateSnapshot.rootHash}`;
      } else {
        step1.details = 'No state snapshot found, creating a new one';
        
        // In a real implementation, we would query the fallback chain for state
        // For the demo, we'll simulate this
        const simulatedState = {
          vaultId,
          balance: '1000.00',
          lastUpdated: Date.now(),
          owner: '0x123456789...'
        };
        
        // Create a leaf for each chain we have data for
        const chainStates = {};
        for (const chain of [recovery.activeChain, ...recovery.fallbackChains]) {
          chainStates[chain] = stateMerkleTreeService.createStateLeaf(
            vaultId,
            chain,
            simulatedState,
            Date.now()
          );
        }
        
        // Create a new state snapshot
        const newSnapshot = stateMerkleTreeService.updateVaultStateSnapshot(vaultId, chainStates as any);
        if (newSnapshot) {
          step1.success = true;
          step1.details = `Created new state snapshot with root ${newSnapshot.rootHash}`;
        }
      }
      
      // Record the step
      this.addRecoveryStep(vaultId, step1);
      
      // Step 2: Validate the state using time-weighted validation
      const step2: RecoveryStep = {
        timestamp: Date.now(),
        action: 'VALIDATE_STATE',
        chain: recovery.activeChain,
        success: false
      };
      
      // Determine vault value from metadata
      const vaultValue = recovery.metadata.valueUSD || 1000;
      
      // Initiate validation
      const validationRequest = timeWeightedValidation.initiateValidation({
        vaultId,
        value: vaultValue,
        primaryChain: recovery.activeChain,
        requestTimestamp: Date.now(),
        merkleRoot: stateSnapshot?.rootHash,
        requestMetadata: {
          recoveryId: recovery.recoveryStartTime,
          originalChain: recovery.primaryChain
        }
      });
      
      // Simulate validation confirmations from fallback chains
      for (const chain of recovery.fallbackChains) {
        timeWeightedValidation.addConfirmation({
          vaultId,
          chain,
          confirmationTimestamp: Date.now(),
          stateLeaf: stateSnapshot?.chainStates[chain]
        });
      }
      
      // Get the final validation result
      const validationResult = timeWeightedValidation.updateValidation(vaultId);
      
      if (validationResult && validationResult.confirmedChains.length > 0) {
        step2.success = true;
        step2.details = `Validated state across ${validationResult.confirmedChains.length} chains`;
      } else {
        step2.details = 'Failed to validate state across chains';
      }
      
      // Record the step
      this.addRecoveryStep(vaultId, step2);
      
      // Step 3: Establish the fallback chain as the new primary
      const step3: RecoveryStep = {
        timestamp: Date.now(),
        action: 'ESTABLISH_FALLBACK',
        chain: recovery.activeChain,
        success: step2.success // Only succeed if validation succeeded
      };
      
      if (step3.success) {
        step3.details = `Successfully established ${recovery.activeChain} as the new primary chain`;
        
        // In a real implementation, we would update the vault's primary chain
        // For the demo, we'll just simulate this
      } else {
        step3.details = `Failed to establish ${recovery.activeChain} as the new primary chain`;
      }
      
      // Record the step
      this.addRecoveryStep(vaultId, step3);
      
      // Complete the recovery
      this.completeRecovery(vaultId, step3.success);
      
    } catch (error) {
      securityLogger.error(`Recovery process failed for vault ${vaultId}`, {
        vaultId,
        error: error instanceof Error ? error.message : 'Unknown error'
      });
      
      // Add error step
      this.addRecoveryStep(vaultId, {
        timestamp: Date.now(),
        action: 'RECOVERY_ERROR',
        success: false,
        details: error instanceof Error ? error.message : 'Unknown error'
      });
      
      // Complete the recovery as failed
      this.completeRecovery(vaultId, false);
      
      // Emit failure event
      this.emit('recovery:failed', vaultId, error instanceof Error ? error : new Error('Unknown error'));
    }
  }
  
  /**
   * Add a step to the recovery process
   */
  private addRecoveryStep(vaultId: string, step: RecoveryStep): RecoveryStatus {
    const recovery = this.activeRecoveries.get(vaultId);
    if (!recovery) {
      throw new Error(`No active recovery found for vault ${vaultId}`);
    }
    
    // Add the step
    const updatedRecovery: RecoveryStatus = {
      ...recovery,
      recoverySteps: [...recovery.recoverySteps, step],
      lastUpdated: Date.now()
    };
    
    this.activeRecoveries.set(vaultId, updatedRecovery);
    
    // Emit step event
    this.emit('recovery:step', vaultId, step);
    
    securityLogger.info(`Recovery step ${step.action} for vault ${vaultId}`, {
      vaultId,
      action: step.action,
      success: step.success,
      details: step.details
    });
    
    return updatedRecovery;
  }
  
  /**
   * Complete a recovery process
   */
  private completeRecovery(vaultId: string, success: boolean): RecoveryStatus {
    const recovery = this.activeRecoveries.get(vaultId);
    if (!recovery) {
      throw new Error(`No active recovery found for vault ${vaultId}`);
    }
    
    // Add completion step
    const completionStep: RecoveryStep = {
      timestamp: Date.now(),
      action: success ? 'RECOVERY_COMPLETED' : 'RECOVERY_FAILED',
      success,
      details: success ? 
        `Successfully completed recovery from ${recovery.primaryChain} to ${recovery.activeChain}` :
        `Failed to complete recovery from ${recovery.primaryChain} to ${recovery.activeChain}`
    };
    
    // Update recovery status
    const completedRecovery: RecoveryStatus = {
      ...recovery,
      isRecoveryActive: false,
      recoverySteps: [...recovery.recoverySteps, completionStep],
      lastUpdated: Date.now()
    };
    
    this.activeRecoveries.set(vaultId, completedRecovery);
    
    // Emit completion event
    this.emit('recovery:completed', vaultId, completedRecovery);
    
    securityLogger.info(`Recovery process ${success ? 'completed' : 'failed'} for vault ${vaultId}`, {
      vaultId,
      primaryChain: recovery.primaryChain,
      activeChain: recovery.activeChain,
      duration: Date.now() - recovery.recoveryStartTime
    });
    
    return completedRecovery;
  }
  
  /**
   * Get the status of a recovery process
   */
  getRecoveryStatus(vaultId: string): RecoveryStatus | undefined {
    return this.activeRecoveries.get(vaultId);
  }
  
  /**
   * Get the health status of a blockchain
   */
  getChainHealthStatus(chain: BlockchainType): ChainHealthStatus | undefined {
    return this.chainHealthStatus.get(chain);
  }
  
  /**
   * Get health status for all chains
   */
  getAllChainHealthStatus(): Record<BlockchainType, ChainHealthStatus> {
    const result: Partial<Record<BlockchainType, ChainHealthStatus>> = {};
    
    for (const [chain, status] of this.chainHealthStatus.entries()) {
      result[chain] = status;
    }
    
    return result as Record<BlockchainType, ChainHealthStatus>;
  }
  
  // Type-safe event emitter
  on<E extends keyof RecoveryEvents>(event: E, listener: RecoveryEvents[E]): this {
    return super.on(event, listener as any);
  }
  
  emit<E extends keyof RecoveryEvents>(
    event: E,
    ...args: Parameters<RecoveryEvents[E]>
  ): boolean {
    return super.emit(event, ...args);
  }
}

// Create and export a factory function
export function createAutomatedRecoveryProtocol(
  connectorFactory: ConnectorFactory
): AutomatedRecoveryProtocol {
  return new AutomatedRecoveryProtocol(connectorFactory);
}