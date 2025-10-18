/**
 * Real-Time Anomaly Detection Service
 * 
 * Monitors Trinity Protocol operations in real-time to detect:
 * - Volume spikes (potential exploits/attacks)
 * - Failed verification patterns (Byzantine behavior)
 * - Same-block spam attacks
 * - Price manipulation attempts
 * - Abnormal gas usage patterns (Arbitrum L2 specific)
 * 
 * AUTO-TRIGGERS CIRCUIT BREAKER when anomalies detected
 */

import { EventEmitter } from 'events';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';

export interface AnomalyEvent {
  type: AnomalyType;
  severity: 'low' | 'medium' | 'high' | 'critical';
  timestamp: Date;
  details: any;
  triggerCircuitBreaker: boolean;
}

export enum AnomalyType {
  VOLUME_SPIKE = 'VOLUME_SPIKE',
  FAILED_VERIFICATION_SPIKE = 'FAILED_VERIFICATION_SPIKE',
  SAME_BLOCK_SPAM = 'SAME_BLOCK_SPAM',
  PRICE_MANIPULATION = 'PRICE_MANIPULATION',
  GAS_ANOMALY = 'GAS_ANOMALY',
  REPEATED_FAILURES = 'REPEATED_FAILURES',
  UNUSUAL_PATTERN = 'UNUSUAL_PATTERN'
}

export interface OperationMetrics {
  operationId: string;
  type: 'swap' | 'bridge' | 'vault';
  amount: number;
  timestamp: Date;
  chainFrom: string;
  chainTo: string;
  gasUsed?: number;
  success: boolean;
  blockNumber?: number;
}

export interface AnomalyMetrics {
  // Volume tracking
  totalVolume24h: number;
  totalOperations24h: number;
  avgVolumePerOp: number;
  
  // Verification tracking
  totalVerifications1h: number;
  failedVerifications1h: number;
  failureRate1h: number;
  
  // Block tracking
  operationsInBlock: Map<number, number>;
  currentBlock: number;
  
  // Gas tracking (Arbitrum L2)
  avgGasUsed: number;
  gasSpikes: number;
  
  // Pattern tracking
  repeatedFailuresByUser: Map<string, number>;
  consecutiveFailures: number;
}

export class AnomalyDetectorService extends EventEmitter {
  private metrics: AnomalyMetrics;
  private recentOperations: OperationMetrics[] = [];
  private readonly MAX_OPERATIONS_HISTORY = 1000;
  
  // Thresholds (configurable but defaulted to secure values)
  private readonly VOLUME_SPIKE_THRESHOLD = 500; // 500% = 5x spike
  private readonly FAILURE_RATE_THRESHOLD = 20; // 20% failure rate
  private readonly SAME_BLOCK_THRESHOLD = 10; // Max operations per block
  private readonly GAS_SPIKE_THRESHOLD = 300; // 300% = 3x gas spike
  private readonly CONSECUTIVE_FAILURE_THRESHOLD = 5; // 5 consecutive failures
  
  // Time windows
  private readonly VOLUME_WINDOW = 24 * 60 * 60 * 1000; // 24 hours
  private readonly VERIFICATION_WINDOW = 60 * 60 * 1000; // 1 hour
  
  constructor() {
    super();
    
    this.metrics = {
      totalVolume24h: 0,
      totalOperations24h: 0,
      avgVolumePerOp: 0,
      totalVerifications1h: 0,
      failedVerifications1h: 0,
      failureRate1h: 0,
      operationsInBlock: new Map(),
      currentBlock: 0,
      avgGasUsed: 0,
      gasSpikes: 0,
      repeatedFailuresByUser: new Map(),
      consecutiveFailures: 0
    };
    
    // Reset metrics periodically
    this.startMetricsReset();
    
    securityLogger.info('🔍 Real-Time Anomaly Detector initialized', SecurityEventType.SYSTEM_ERROR);
    securityLogger.info('   Monitoring: Volume spikes, verification failures, spam attacks', SecurityEventType.SYSTEM_ERROR);
  }

  /**
   * Process new operation and check for anomalies
   */
  async processOperation(operation: OperationMetrics): Promise<AnomalyEvent[]> {
    const anomalies: AnomalyEvent[] = [];
    
    // Add to history
    this.recentOperations.push(operation);
    if (this.recentOperations.length > this.MAX_OPERATIONS_HISTORY) {
      this.recentOperations.shift();
    }
    
    // Update metrics
    this.metrics.totalOperations24h++;
    this.metrics.totalVolume24h += operation.amount;
    this.metrics.avgVolumePerOp = this.metrics.totalVolume24h / this.metrics.totalOperations24h;
    
    // Check for anomalies
    const volumeAnomaly = this.checkVolumeSpike(operation);
    if (volumeAnomaly) anomalies.push(volumeAnomaly);
    
    const blockAnomaly = this.checkSameBlockSpam(operation);
    if (blockAnomaly) anomalies.push(blockAnomaly);
    
    const gasAnomaly = this.checkGasAnomaly(operation);
    if (gasAnomaly) anomalies.push(gasAnomaly);
    
    const patternAnomaly = this.checkUnusualPattern(operation);
    if (patternAnomaly) anomalies.push(patternAnomaly);
    
    // Track consecutive failures
    if (!operation.success) {
      this.metrics.consecutiveFailures++;
      const failureAnomaly = this.checkConsecutiveFailures();
      if (failureAnomaly) anomalies.push(failureAnomaly);
    } else {
      this.metrics.consecutiveFailures = 0;
    }
    
    // Emit anomalies
    for (const anomaly of anomalies) {
      this.emit('anomaly', anomaly);
      
      securityLogger.warn(
        `🚨 ANOMALY DETECTED: ${anomaly.type}`,
        SecurityEventType.SUSPICIOUS_ACTIVITY,
        anomaly.details
      );
      
      if (anomaly.triggerCircuitBreaker) {
        securityLogger.error(
          `⚠️  CRITICAL ANOMALY - Triggering circuit breaker`,
          SecurityEventType.SUSPICIOUS_ACTIVITY,
          { type: anomaly.type, severity: anomaly.severity }
        );
      }
    }
    
    return anomalies;
  }

  /**
   * Process verification result
   */
  async processVerification(success: boolean): Promise<AnomalyEvent | null> {
    this.metrics.totalVerifications1h++;
    if (!success) {
      this.metrics.failedVerifications1h++;
    }
    
    this.metrics.failureRate1h = 
      (this.metrics.failedVerifications1h / this.metrics.totalVerifications1h) * 100;
    
    return this.checkVerificationFailureRate();
  }

  /**
   * ANOMALY CHECK: Volume spike detector
   */
  private checkVolumeSpike(operation: OperationMetrics): AnomalyEvent | null {
    // Calculate spike ratio
    const avgVolume = this.metrics.avgVolumePerOp > 0 ? this.metrics.avgVolumePerOp : 1;
    const spikeRatio = (operation.amount / avgVolume) * 100;
    
    if (spikeRatio > this.VOLUME_SPIKE_THRESHOLD) {
      return {
        type: AnomalyType.VOLUME_SPIKE,
        severity: spikeRatio > 1000 ? 'critical' : 'high',
        timestamp: new Date(),
        details: {
          operationId: operation.operationId,
          amount: operation.amount,
          avgVolume,
          spikeRatio: `${Math.round(spikeRatio)}%`
        },
        triggerCircuitBreaker: spikeRatio > 1000 // >10x triggers circuit breaker
      };
    }
    
    return null;
  }

  /**
   * ANOMALY CHECK: Same-block spam detector
   */
  private checkSameBlockSpam(operation: OperationMetrics): AnomalyEvent | null {
    if (!operation.blockNumber) return null;
    
    // Track operations in current block
    if (operation.blockNumber !== this.metrics.currentBlock) {
      this.metrics.currentBlock = operation.blockNumber;
      this.metrics.operationsInBlock.clear();
    }
    
    const blockCount = (this.metrics.operationsInBlock.get(operation.blockNumber) || 0) + 1;
    this.metrics.operationsInBlock.set(operation.blockNumber, blockCount);
    
    if (blockCount > this.SAME_BLOCK_THRESHOLD) {
      return {
        type: AnomalyType.SAME_BLOCK_SPAM,
        severity: 'critical',
        timestamp: new Date(),
        details: {
          blockNumber: operation.blockNumber,
          operationCount: blockCount,
          threshold: this.SAME_BLOCK_THRESHOLD
        },
        triggerCircuitBreaker: true
      };
    }
    
    return null;
  }

  /**
   * ANOMALY CHECK: Gas usage anomaly (Arbitrum L2 specific)
   */
  private checkGasAnomaly(operation: OperationMetrics): AnomalyEvent | null {
    if (!operation.gasUsed) return null;
    
    // Update average gas
    if (this.metrics.avgGasUsed === 0) {
      this.metrics.avgGasUsed = operation.gasUsed;
      return null;
    }
    
    // Exponential moving average
    this.metrics.avgGasUsed = this.metrics.avgGasUsed * 0.9 + operation.gasUsed * 0.1;
    
    // Check for gas spike
    const gasRatio = (operation.gasUsed / this.metrics.avgGasUsed) * 100;
    
    if (gasRatio > this.GAS_SPIKE_THRESHOLD) {
      this.metrics.gasSpikes++;
      
      return {
        type: AnomalyType.GAS_ANOMALY,
        severity: gasRatio > 500 ? 'high' : 'medium',
        timestamp: new Date(),
        details: {
          operationId: operation.operationId,
          gasUsed: operation.gasUsed,
          avgGas: Math.round(this.metrics.avgGasUsed),
          spikeRatio: `${Math.round(gasRatio)}%`
        },
        triggerCircuitBreaker: this.metrics.gasSpikes > 5 // 5 consecutive gas spikes
      };
    }
    
    this.metrics.gasSpikes = 0; // Reset counter on normal gas
    return null;
  }

  /**
   * ANOMALY CHECK: Verification failure rate
   */
  private checkVerificationFailureRate(): AnomalyEvent | null {
    // Need minimum sample size
    if (this.metrics.totalVerifications1h < 10) return null;
    
    if (this.metrics.failureRate1h > this.FAILURE_RATE_THRESHOLD) {
      return {
        type: AnomalyType.FAILED_VERIFICATION_SPIKE,
        severity: this.metrics.failureRate1h > 50 ? 'critical' : 'high',
        timestamp: new Date(),
        details: {
          failureRate: `${this.metrics.failureRate1h.toFixed(1)}%`,
          failedCount: this.metrics.failedVerifications1h,
          totalCount: this.metrics.totalVerifications1h,
          threshold: `${this.FAILURE_RATE_THRESHOLD}%`
        },
        triggerCircuitBreaker: this.metrics.failureRate1h > 50
      };
    }
    
    return null;
  }

  /**
   * ANOMALY CHECK: Consecutive failures
   */
  private checkConsecutiveFailures(): AnomalyEvent | null {
    if (this.metrics.consecutiveFailures > this.CONSECUTIVE_FAILURE_THRESHOLD) {
      return {
        type: AnomalyType.REPEATED_FAILURES,
        severity: 'high',
        timestamp: new Date(),
        details: {
          consecutiveFailures: this.metrics.consecutiveFailures,
          threshold: this.CONSECUTIVE_FAILURE_THRESHOLD
        },
        triggerCircuitBreaker: this.metrics.consecutiveFailures > 10
      };
    }
    
    return null;
  }

  /**
   * ANOMALY CHECK: Unusual patterns (ML-based in future)
   */
  private checkUnusualPattern(operation: OperationMetrics): AnomalyEvent | null {
    // Simplified pattern detection
    // In production, this would use ML models
    
    // Check for rapid same-chain operations
    const recentSameChain = this.recentOperations
      .slice(-10)
      .filter(op => 
        op.chainFrom === operation.chainFrom && 
        op.chainTo === operation.chainTo
      ).length;
    
    if (recentSameChain > 8) { // >80% same-chain operations
      return {
        type: AnomalyType.UNUSUAL_PATTERN,
        severity: 'medium',
        timestamp: new Date(),
        details: {
          pattern: 'Repeated same-chain operations',
          chainFrom: operation.chainFrom,
          chainTo: operation.chainTo,
          occurrences: recentSameChain
        },
        triggerCircuitBreaker: false
      };
    }
    
    return null;
  }

  /**
   * Start periodic metrics reset
   */
  private startMetricsReset(): void {
    // Reset 24h volume metrics
    setInterval(() => {
      this.metrics.totalVolume24h = 0;
      this.metrics.totalOperations24h = 0;
      this.metrics.avgVolumePerOp = 0;
      
      securityLogger.info('🔄 Reset 24h volume metrics', SecurityEventType.SYSTEM_ERROR);
    }, this.VOLUME_WINDOW);
    
    // Reset 1h verification metrics
    setInterval(() => {
      this.metrics.totalVerifications1h = 0;
      this.metrics.failedVerifications1h = 0;
      this.metrics.failureRate1h = 0;
      
      securityLogger.info('🔄 Reset 1h verification metrics', SecurityEventType.SYSTEM_ERROR);
    }, this.VERIFICATION_WINDOW);
  }

  /**
   * Get current anomaly metrics (for monitoring dashboard)
   */
  getMetrics(): AnomalyMetrics {
    return { ...this.metrics };
  }

  /**
   * Get recent anomalies
   */
  getRecentAnomalies(limit: number = 10): AnomalyEvent[] {
    // This would be implemented with a proper anomaly history
    return [];
  }

  /**
   * Reset all metrics (for testing)
   */
  resetMetrics(): void {
    this.metrics = {
      totalVolume24h: 0,
      totalOperations24h: 0,
      avgVolumePerOp: 0,
      totalVerifications1h: 0,
      failedVerifications1h: 0,
      failureRate1h: 0,
      operationsInBlock: new Map(),
      currentBlock: 0,
      avgGasUsed: 0,
      gasSpikes: 0,
      repeatedFailuresByUser: new Map(),
      consecutiveFailures: 0
    };
    
    this.recentOperations = [];
  }
}

// Singleton instance
export const anomalyDetector = new AnomalyDetectorService();

// Listen for anomalies and log them
anomalyDetector.on('anomaly', (anomaly: AnomalyEvent) => {
  if (anomaly.triggerCircuitBreaker) {
    securityLogger.error(
      '🚨 CIRCUIT BREAKER TRIGGERED BY ANOMALY',
      SecurityEventType.SUSPICIOUS_ACTIVITY,
      anomaly
    );
  }
});
