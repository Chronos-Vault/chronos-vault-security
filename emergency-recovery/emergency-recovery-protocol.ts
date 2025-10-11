/**
 * Emergency Recovery Protocol
 * 
 * Automated failover and recovery when chains fail
 * Part of Trinity Protocol Emergency Recovery System
 * 
 * Features:
 * - Automated failover when chains go down
 * - Recovery coordination across remaining healthy chains
 * - State preservation during failures
 * - Graceful degradation strategies
 */

import { EventEmitter } from 'events';
import { circuitBreakerService, ChainStatus } from './circuit-breaker-service';
import { trinityProtocol, OperationType } from '../security/trinity-protocol';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';

export enum RecoveryMode {
  NORMAL = 'NORMAL',           // All 3 chains operational
  DEGRADED = 'DEGRADED',       // 2 chains operational
  CRITICAL = 'CRITICAL',       // Only 1 chain operational
  EMERGENCY = 'EMERGENCY'      // Manual intervention required
}

export interface RecoveryStatus {
  mode: RecoveryMode;
  healthyChains: string[];
  failedChains: string[];
  degradedChains: string[];
  canOperate: boolean;
  requiresIntervention: boolean;
  timestamp: number;
}

export class EmergencyRecoveryProtocol extends EventEmitter {
  private currentMode: RecoveryMode = RecoveryMode.NORMAL;
  private isActive: boolean = false;
  private recoveryAttempts: Map<string, number> = new Map();
  private readonly MAX_RECOVERY_ATTEMPTS = 3;

  constructor() {
    super();
  }

  /**
   * Start the emergency recovery protocol
   */
  async start(): Promise<void> {
    if (this.isActive) {
      securityLogger.warn('Emergency Recovery Protocol already active', SecurityEventType.CROSS_CHAIN_VERIFICATION);
      return;
    }

    securityLogger.info('🚑 Emergency Recovery Protocol started', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    this.isActive = true;

    // Listen to circuit breaker events
    this.setupCircuitBreakerListeners();

    // Start circuit breaker monitoring
    await circuitBreakerService.startMonitoring();
  }

  /**
   * Stop the emergency recovery protocol
   */
  stop(): void {
    if (!this.isActive) {
      return;
    }

    circuitBreakerService.stopMonitoring();
    circuitBreakerService.removeAllListeners();
    this.isActive = false;

    securityLogger.info('🛑 Emergency Recovery Protocol stopped', SecurityEventType.CROSS_CHAIN_VERIFICATION);
  }

  /**
   * Setup circuit breaker listeners
   */
  private setupCircuitBreakerListeners(): void {
    // Chain degraded
    circuitBreakerService.on('chain:degraded', async (data) => {
      await this.handleChainDegraded(data.chain);
    });

    // Chain failed
    circuitBreakerService.on('chain:failed', async (data) => {
      await this.handleChainFailed(data.chain);
    });

    // Chain recovered
    circuitBreakerService.on('chain:recovered', async (data) => {
      await this.handleChainRecovered(data.chain);
    });

    // Trinity Protocol degraded (2/3 chains healthy)
    circuitBreakerService.on('trinity:degraded', async (data) => {
      await this.handleTrinityDegraded(data);
    });

    // Trinity Protocol critical (< 2 chains healthy)
    circuitBreakerService.on('trinity:critical', async (data) => {
      await this.handleTrinityCritical(data);
    });

    // Emergency activation requested
    circuitBreakerService.on('emergency:activate', async (data) => {
      await this.activateEmergencyMode(data);
    });
  }

  /**
   * Handle chain degraded
   */
  private async handleChainDegraded(chain: string): Promise<void> {
    securityLogger.warn(`⚠️ Chain degraded: ${chain}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Check if recovery needed
    const status = this.getRecoveryStatus();
    
    if (status.mode === RecoveryMode.NORMAL) {
      // Still operational, no action needed yet
      securityLogger.info(`   Trinity Protocol still operational (${status.healthyChains.length}/3 healthy)`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    }
  }

  /**
   * Handle chain failed
   */
  private async handleChainFailed(chain: string): Promise<void> {
    securityLogger.error(`🚨 Chain failed: ${chain}`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    
    // Attempt automated recovery
    await this.attemptChainRecovery(chain);
    
    // Re-evaluate Trinity Protocol status
    const status = this.getRecoveryStatus();
    this.updateRecoveryMode(status);
    
    this.emit('recovery:status-changed', status);
  }

  /**
   * Handle chain recovered
   */
  private async handleChainRecovered(chain: string): Promise<void> {
    securityLogger.info(`✅ Chain recovered: ${chain}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Reset recovery attempts
    this.recoveryAttempts.delete(chain);
    
    // Re-evaluate Trinity Protocol status
    const status = this.getRecoveryStatus();
    this.updateRecoveryMode(status);
    
    this.emit('recovery:status-changed', status);
  }

  /**
   * Handle Trinity Protocol degraded (2/3 chains)
   */
  private async handleTrinityDegraded(data: any): Promise<void> {
    securityLogger.warn(`⚠️ Trinity Protocol DEGRADED: ${data.healthyChains} chains healthy`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    this.currentMode = RecoveryMode.DEGRADED;
    
    securityLogger.warn(`   Operating with reduced redundancy`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    securityLogger.warn(`   Failed chains: ${data.failedChains.map((c: any) => c.chain).join(', ')}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Trigger recovery for failed chains
    for (const failed of data.failedChains) {
      await this.attemptChainRecovery(failed.chain);
    }
  }

  /**
   * Handle Trinity Protocol critical (< 2 chains)
   */
  private async handleTrinityCritical(data: any): Promise<void> {
    securityLogger.error(`🚨 Trinity Protocol CRITICAL: Only ${data.healthyChains} chains healthy`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    
    this.currentMode = RecoveryMode.CRITICAL;
    
    securityLogger.error(`   2-of-3 consensus NOT POSSIBLE`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    securityLogger.error(`   Vault operations SUSPENDED`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    
    // Attempt aggressive recovery
    for (const failed of data.failedChains) {
      await this.attemptChainRecovery(failed.chain, true);
    }
    
    this.emit('protocol:critical', data);
  }

  /**
   * Activate emergency mode
   */
  private async activateEmergencyMode(data: any): Promise<void> {
    this.currentMode = RecoveryMode.EMERGENCY;
    
    securityLogger.error(`🚨 EMERGENCY MODE ACTIVATED`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    securityLogger.error(`   ${data.failedChains.length} chains failed`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    securityLogger.error(`   Manual intervention REQUIRED`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    
    this.emit('emergency:activated', {
      failedChains: data.failedChains,
      timestamp: Date.now()
    });
  }

  /**
   * Attempt chain recovery
   */
  private async attemptChainRecovery(chain: string, aggressive: boolean = false): Promise<void> {
    const attempts = this.recoveryAttempts.get(chain) || 0;
    
    if (attempts >= this.MAX_RECOVERY_ATTEMPTS && !aggressive) {
      securityLogger.error(`   Max recovery attempts reached for ${chain}`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      return;
    }

    this.recoveryAttempts.set(chain, attempts + 1);
    
    securityLogger.info(`🔄 Attempting recovery for ${chain} (attempt ${attempts + 1}/${this.MAX_RECOVERY_ATTEMPTS})`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    
    // Attempt to reset circuit breaker
    try {
      circuitBreakerService.resetCircuit(chain as any);
      
      // Wait a bit for chain to stabilize
      await new Promise(resolve => setTimeout(resolve, 2000));
      
      // Check if recovery successful
      const health = circuitBreakerService.getChainHealth(chain as any);
      
      if (health && health.status === ChainStatus.HEALTHY) {
        securityLogger.info(`   ✅ ${chain} recovery successful`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
        this.recoveryAttempts.delete(chain);
      } else {
        securityLogger.warn(`   ⚠️ ${chain} recovery incomplete`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
      }
    } catch (error) {
      securityLogger.error(`   ❌ ${chain} recovery failed`, SecurityEventType.SYSTEM_ERROR, error);
    }
  }

  /**
   * Get current recovery status
   */
  getRecoveryStatus(): RecoveryStatus {
    const trinityStatus = circuitBreakerService.getTrinityStatus();
    const allHealth = circuitBreakerService.getAllChainHealth();
    
    const healthyChains = allHealth
      .filter(h => h.status === ChainStatus.HEALTHY)
      .map(h => h.chain);
    
    const failedChains = allHealth
      .filter(h => h.status === ChainStatus.FAILED)
      .map(h => h.chain);
    
    const degradedChains = allHealth
      .filter(h => h.status === ChainStatus.DEGRADED)
      .map(h => h.chain);

    // Determine recovery mode
    let mode: RecoveryMode;
    if (healthyChains.length === 3) {
      mode = RecoveryMode.NORMAL;
    } else if (healthyChains.length === 2) {
      mode = RecoveryMode.DEGRADED;
    } else if (healthyChains.length === 1) {
      mode = RecoveryMode.CRITICAL;
    } else {
      mode = RecoveryMode.EMERGENCY;
    }

    const canOperate = healthyChains.length >= 2;
    const requiresIntervention = healthyChains.length < 2;

    return {
      mode,
      healthyChains,
      failedChains,
      degradedChains,
      canOperate,
      requiresIntervention,
      timestamp: Date.now()
    };
  }

  /**
   * Update recovery mode
   */
  private updateRecoveryMode(status: RecoveryStatus): void {
    const previousMode = this.currentMode;
    this.currentMode = status.mode;

    if (previousMode !== status.mode) {
      securityLogger.info(`🔄 Recovery mode changed: ${previousMode} → ${status.mode}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    }
  }

  /**
   * Execute emergency vault recovery
   */
  async executeEmergencyVaultRecovery(vaultId: string, recoveryKey: string): Promise<boolean> {
    securityLogger.warn(`🚨 Executing emergency vault recovery: ${vaultId}`, SecurityEventType.SUSPICIOUS_ACTIVITY);
    
    try {
      const result = await trinityProtocol.emergencyRecovery(vaultId, recoveryKey);
      
      if (result.consensusReached) {
        securityLogger.info(`   ✅ Emergency recovery approved by Trinity Protocol`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
        return true;
      } else {
        securityLogger.warn(`   ❌ Emergency recovery denied - insufficient consensus`, SecurityEventType.SUSPICIOUS_ACTIVITY);
        return false;
      }
    } catch (error) {
      securityLogger.error(`   ❌ Emergency recovery failed`, SecurityEventType.SYSTEM_ERROR, error);
      return false;
    }
  }

  /**
   * Get current recovery mode
   */
  getCurrentMode(): RecoveryMode {
    return this.currentMode;
  }
}

export const emergencyRecoveryProtocol = new EmergencyRecoveryProtocol();
