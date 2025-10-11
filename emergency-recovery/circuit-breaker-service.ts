/**
 * Circuit Breaker Service
 * 
 * Auto-detects chain failures and triggers emergency protocols
 * Part of Trinity Protocol Emergency Recovery System
 * 
 * Features:
 * - Real-time chain health monitoring
 * - Automatic failure detection
 * - Circuit breaker pattern for graceful degradation
 * - Emergency protocol activation
 */

import { EventEmitter } from 'events';
import { trinityProtocol } from '../security/trinity-protocol';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';

export enum ChainStatus {
  HEALTHY = 'HEALTHY',
  DEGRADED = 'DEGRADED',
  FAILED = 'FAILED',
  RECOVERING = 'RECOVERING'
}

export enum CircuitState {
  CLOSED = 'CLOSED',      // Normal operation
  OPEN = 'OPEN',          // Circuit open, blocking requests
  HALF_OPEN = 'HALF_OPEN' // Testing if service recovered
}

export interface ChainHealth {
  chain: 'arbitrum' | 'solana' | 'ton';
  status: ChainStatus;
  circuitState: CircuitState;
  failureCount: number;
  lastFailure: number;
  lastSuccess: number;
  responseTime: number;
}

export class CircuitBreakerService extends EventEmitter {
  private chainHealth: Map<string, ChainHealth> = new Map();
  private monitoringInterval: NodeJS.Timeout | null = null;
  private isMonitoring: boolean = false;

  // Circuit breaker configuration
  private readonly FAILURE_THRESHOLD = 3;
  private readonly TIMEOUT_THRESHOLD = 5000; // 5 seconds
  private readonly RESET_TIMEOUT = 30000; // 30 seconds
  private readonly HALF_OPEN_TIMEOUT = 10000; // 10 seconds

  constructor() {
    super();
    
    // Initialize chain health tracking
    this.initializeChainHealth();
  }

  /**
   * Initialize chain health tracking
   */
  private initializeChainHealth(): void {
    const chains: Array<'arbitrum' | 'solana' | 'ton'> = ['arbitrum', 'solana', 'ton'];
    
    chains.forEach(chain => {
      this.chainHealth.set(chain, {
        chain,
        status: ChainStatus.HEALTHY,
        circuitState: CircuitState.CLOSED,
        failureCount: 0,
        lastFailure: 0,
        lastSuccess: Date.now(),
        responseTime: 0
      });
    });
  }

  /**
   * Start monitoring chain health (idempotent)
   */
  async startMonitoring(): Promise<void> {
    // Idempotent: silently return if already monitoring
    // This is safe since multiple services may call startMonitoring()
    if (this.isMonitoring) {
      return;
    }

    securityLogger.info('🔌 Circuit Breaker Service started - monitoring chain health', SecurityEventType.CROSS_CHAIN_VERIFICATION);
    this.isMonitoring = true;

    // Monitor every 5 seconds
    this.monitoringInterval = setInterval(() => this.checkAllChains(), 5000);
    
    // Initial check
    await this.checkAllChains();
  }

  /**
   * Stop monitoring
   */
  stopMonitoring(): void {
    if (this.monitoringInterval) {
      clearInterval(this.monitoringInterval);
      this.monitoringInterval = null;
    }

    this.isMonitoring = false;
    securityLogger.info('🛑 Circuit Breaker Service stopped', SecurityEventType.CROSS_CHAIN_VERIFICATION);
  }

  /**
   * Check all chain health
   */
  private async checkAllChains(): Promise<void> {
    const chains: Array<'arbitrum' | 'solana' | 'ton'> = ['arbitrum', 'solana', 'ton'];
    
    for (const chain of chains) {
      await this.checkChainHealth(chain);
    }

    // Evaluate Trinity Protocol status
    await this.evaluateTrinityProtocolHealth();
  }

  /**
   * Check individual chain health
   */
  private async checkChainHealth(chain: 'arbitrum' | 'solana' | 'ton'): Promise<void> {
    const health = this.chainHealth.get(chain);
    if (!health) return;

    // Skip if circuit is open and timeout hasn't expired
    if (health.circuitState === CircuitState.OPEN) {
      const timeSinceFailure = Date.now() - health.lastFailure;
      
      if (timeSinceFailure < this.RESET_TIMEOUT) {
        return; // Still in timeout period
      } else {
        // Timeout expired, move to half-open state
        health.circuitState = CircuitState.HALF_OPEN;
        securityLogger.info(`⚡ ${chain} circuit moved to HALF_OPEN state`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
      }
    }

    try {
      const startTime = Date.now();
      
      // Perform health check based on chain
      const isHealthy = await this.performHealthCheck(chain);
      
      const responseTime = Date.now() - startTime;
      health.responseTime = responseTime;

      if (isHealthy && responseTime < this.TIMEOUT_THRESHOLD) {
        // Success
        this.recordSuccess(chain);
      } else {
        // Failure (either unhealthy or timeout)
        this.recordFailure(chain, responseTime >= this.TIMEOUT_THRESHOLD ? 'timeout' : 'unhealthy');
      }
    } catch (error) {
      this.recordFailure(chain, 'error');
      securityLogger.error(`Health check failed for ${chain}`, SecurityEventType.SYSTEM_ERROR, error);
    }
  }

  /**
   * Perform health check on specific chain
   */
  private async performHealthCheck(chain: 'arbitrum' | 'solana' | 'ton'): Promise<boolean> {
    const healthStatus = await trinityProtocol.healthCheck();
    
    switch (chain) {
      case 'arbitrum':
        return healthStatus.ethereum;
      case 'solana':
        return healthStatus.solana;
      case 'ton':
        return healthStatus.ton;
      default:
        return false;
    }
  }

  /**
   * Record successful health check
   */
  private recordSuccess(chain: string): void {
    const health = this.chainHealth.get(chain);
    if (!health) return;

    const previousState = health.circuitState;

    health.failureCount = 0;
    health.lastSuccess = Date.now();
    health.circuitState = CircuitState.CLOSED;

    // Update status
    if (health.status !== ChainStatus.HEALTHY) {
      health.status = ChainStatus.HEALTHY;
      securityLogger.info(`✅ ${chain} recovered - status: HEALTHY`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
      this.emit('chain:recovered', { chain, health });
    }

    // Log state transition
    if (previousState !== CircuitState.CLOSED) {
      securityLogger.info(`⚡ ${chain} circuit CLOSED - normal operation resumed`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
    }
  }

  /**
   * Record failed health check
   */
  private recordFailure(chain: string, reason: string): void {
    const health = this.chainHealth.get(chain);
    if (!health) return;

    health.failureCount++;
    health.lastFailure = Date.now();

    securityLogger.warn(`⚠️ ${chain} health check failed (${reason}) - count: ${health.failureCount}/${this.FAILURE_THRESHOLD}`, SecurityEventType.CROSS_CHAIN_VERIFICATION);

    // Check if threshold reached
    if (health.failureCount >= this.FAILURE_THRESHOLD) {
      this.openCircuit(chain);
    } else {
      // Mark as degraded
      if (health.status !== ChainStatus.DEGRADED) {
        health.status = ChainStatus.DEGRADED;
        securityLogger.warn(`⚠️ ${chain} status: DEGRADED`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
        this.emit('chain:degraded', { chain, health });
      }
    }
  }

  /**
   * Open circuit breaker
   */
  private openCircuit(chain: string): void {
    const health = this.chainHealth.get(chain);
    if (!health) return;

    if (health.circuitState !== CircuitState.OPEN) {
      health.circuitState = CircuitState.OPEN;
      health.status = ChainStatus.FAILED;

      securityLogger.error(`🚨 ${chain} CIRCUIT BREAKER OPEN - chain marked as FAILED`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      securityLogger.error(`   Failure count: ${health.failureCount}`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      securityLogger.error(`   Will retry after ${this.RESET_TIMEOUT / 1000} seconds`, SecurityEventType.SUSPICIOUS_ACTIVITY);

      this.emit('circuit:open', { chain, health });
      this.emit('chain:failed', { chain, health });

      // Trigger emergency protocol if needed
      this.checkEmergencyProtocolActivation();
    }
  }

  /**
   * Evaluate Trinity Protocol health
   */
  private async evaluateTrinityProtocolHealth(): Promise<void> {
    const healthyChains = Array.from(this.chainHealth.values()).filter(
      h => h.status === ChainStatus.HEALTHY
    ).length;

    const failedChains = Array.from(this.chainHealth.values()).filter(
      h => h.status === ChainStatus.FAILED
    );

    if (healthyChains < 2) {
      securityLogger.error(`🚨 TRINITY PROTOCOL CRITICAL: Only ${healthyChains}/3 chains healthy`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      this.emit('trinity:critical', { healthyChains, failedChains });
    } else if (healthyChains === 2) {
      securityLogger.warn(`⚠️ TRINITY PROTOCOL DEGRADED: ${healthyChains}/3 chains healthy`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
      this.emit('trinity:degraded', { healthyChains, failedChains });
    } else {
      // All 3 chains healthy
      this.emit('trinity:healthy', { healthyChains });
    }
  }

  /**
   * Check if emergency protocol should be activated
   */
  private async checkEmergencyProtocolActivation(): Promise<void> {
    const failedChains = Array.from(this.chainHealth.values()).filter(
      h => h.status === ChainStatus.FAILED
    );

    if (failedChains.length >= 2) {
      securityLogger.error(`🚨 EMERGENCY PROTOCOL ACTIVATION: ${failedChains.length} chains failed`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      securityLogger.error(`   Failed chains: ${failedChains.map(h => h.chain).join(', ')}`, SecurityEventType.SUSPICIOUS_ACTIVITY);
      
      this.emit('emergency:activate', { failedChains });
    }
  }

  /**
   * Get chain health status
   */
  getChainHealth(chain: 'arbitrum' | 'solana' | 'ton'): ChainHealth | undefined {
    return this.chainHealth.get(chain);
  }

  /**
   * Get all chain health statuses
   */
  getAllChainHealth(): ChainHealth[] {
    return Array.from(this.chainHealth.values());
  }

  /**
   * Get Trinity Protocol status
   */
  getTrinityStatus(): {
    healthy: boolean;
    healthyChains: number;
    degradedChains: number;
    failedChains: number;
    status: string;
  } {
    const chains = Array.from(this.chainHealth.values());
    const healthyChains = chains.filter(h => h.status === ChainStatus.HEALTHY).length;
    const degradedChains = chains.filter(h => h.status === ChainStatus.DEGRADED).length;
    const failedChains = chains.filter(h => h.status === ChainStatus.FAILED).length;

    let status = 'OPERATIONAL';
    if (failedChains >= 2) {
      status = 'CRITICAL';
    } else if (healthyChains === 2) {
      status = 'DEGRADED';
    }

    return {
      healthy: healthyChains === 3,
      healthyChains,
      degradedChains,
      failedChains,
      status
    };
  }

  /**
   * Manually reset circuit
   */
  resetCircuit(chain: 'arbitrum' | 'solana' | 'ton'): void {
    const health = this.chainHealth.get(chain);
    if (!health) return;

    health.circuitState = CircuitState.CLOSED;
    health.failureCount = 0;
    health.status = ChainStatus.HEALTHY;

    securityLogger.info(`🔄 ${chain} circuit manually reset`, SecurityEventType.CROSS_CHAIN_VERIFICATION);
  }
}

export const circuitBreakerService = new CircuitBreakerService();
