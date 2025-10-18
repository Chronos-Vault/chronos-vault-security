/**
 * Behavioral Analysis Security System
 * 
 * Advanced AI-powered system that monitors user activities and transactions
 * to detect suspicious behavior and potential security threats in real-time.
 */

import { createHash } from 'crypto';
import { BlockchainType, TransactionType } from '../../shared/types';

export enum RiskLevel {
  NONE = 'NONE',
  LOW = 'LOW',
  MEDIUM = 'MEDIUM',
  HIGH = 'HIGH',
  CRITICAL = 'CRITICAL'
}

export enum SecurityAction {
  MONITOR = 'MONITOR',
  ALERT = 'ALERT',
  CHALLENGE = 'CHALLENGE',
  BLOCK = 'BLOCK',
  REPORT = 'REPORT'
}

export interface SecurityAlert {
  id: string;
  timestamp: number;
  userId?: string;
  vaultId?: string;
  transactionId?: string;
  ipAddress?: string;
  riskLevel: RiskLevel;
  description: string;
  detectionMethod: string;
  recommendedAction: SecurityAction;
  falsePositiveProbability: number; // 0-1
  metadata: Record<string, any>;
}

export interface BehavioralPattern {
  patternId: string;
  userId: string;
  transactionFrequency: number; // Avg transactions per day
  chainPreferences: BlockchainType[];
  accessPatterns: {
    deviceTypes: string[];
    geolocations: string[];
    timeRanges: string[];
    browserFingerprints: string[];
  };
  valueDistribution: {
    average: number;
    max: number;
    min: number;
    stdDev: number;
  };
  commonBeneficiaries: string[];
  lastAnalyzed: number;
  confidenceScore: number; // 0-1
}

export interface BehavioralAnalysisConfig {
  enabled: boolean;
  learningMode: boolean;
  sensitivityLevel: number; // 1-10
  minimumConfidenceThreshold: number; // 0-1
  alertThresholds: {
    low: number;
    medium: number;
    high: number;
    critical: number;
  };
  analysisPeriodDays: number;
  storeBehavioralPatternsOnChain: boolean;
}

const DEFAULT_BEHAVIORAL_CONFIG: BehavioralAnalysisConfig = {
  enabled: true,
  learningMode: true,
  sensitivityLevel: 7,
  minimumConfidenceThreshold: 0.7,
  alertThresholds: {
    low: 0.5,
    medium: 0.7,
    high: 0.85,
    critical: 0.95
  },
  analysisPeriodDays: 90,
  storeBehavioralPatternsOnChain: false
};

/**
 * Behavioral Analysis Security System
 * 
 * This system analyzes user behavior patterns to detect anomalies and potential security threats.
 * It uses machine learning algorithms to establish baselines for normal behavior and
 * identifies deviations that might indicate compromise.
 */
export class BehavioralAnalysisSystem {
  private config: BehavioralAnalysisConfig;
  private patterns: Map<string, BehavioralPattern> = new Map();
  private alerts: SecurityAlert[] = [];
  private logger: any; // Would be proper logger
  
  constructor(config: Partial<BehavioralAnalysisConfig> = {}) {
    this.config = { ...DEFAULT_BEHAVIORAL_CONFIG, ...config };
    this.logger = {
      debug: (msg: string) => console.debug(`[BehavioralSecurity] ${msg}`),
      info: (msg: string) => console.info(`[BehavioralSecurity] ${msg}`),
      warn: (msg: string) => console.warn(`[BehavioralSecurity] ${msg}`),
      error: (msg: string, error?: any) => console.error(`[BehavioralSecurity] ${msg}`, error)
    };
    
    this.logger.info(`Behavioral Analysis System initialized with sensitivity ${this.config.sensitivityLevel}`);
  }
  
  /**
   * Initialize the system by loading existing behavioral patterns
   */
  async initialize(): Promise<void> {
    this.logger.info('Initializing Behavioral Analysis System');
    
    try {
      // In production, this would load patterns from the database
      // For demonstration, we'll initialize with an empty patterns map
      this.patterns = new Map();
      
      this.logger.info('Behavioral Analysis System initialized successfully');
    } catch (error) {
      this.logger.error('Failed to initialize Behavioral Analysis System', error);
      throw new Error(`Behavioral analysis initialization failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
  
  /**
   * Analyze a user transaction for suspicious behavior
   */
  async analyzeTransaction(transaction: {
    transactionId: string;
    userId: string;
    vaultId?: string;
    type: TransactionType;
    amount?: number;
    blockchain: BlockchainType;
    timestamp: number;
    ipAddress: string;
    deviceInfo: Record<string, any>;
    geolocation?: string;
  }): Promise<SecurityAlert | null> {
    if (!this.config.enabled) {
      return null;
    }
    
    this.logger.debug(`Analyzing transaction ${transaction.transactionId} for user ${transaction.userId}`);
    
    try {
      // 1. Get or create user's behavioral pattern
      const pattern = await this.getUserBehavioralPattern(transaction.userId);
      
      // 2. Calculate anomaly scores for different aspects of the transaction
      const anomalyScores = {
        value: this.calculateValueAnomaly(transaction.amount || 0, pattern),
        frequency: this.calculateFrequencyAnomaly(transaction.timestamp, pattern),
        geolocation: this.calculateGeolocationAnomaly(transaction.geolocation || '', pattern),
        blockchain: this.calculateBlockchainAnomaly(transaction.blockchain, pattern),
        device: this.calculateDeviceAnomaly(transaction.deviceInfo, pattern)
      };
      
      // 3. Calculate overall anomaly score as weighted average
      const weights = {
        value: 0.3,
        frequency: 0.2,
        geolocation: 0.25,
        blockchain: 0.15,
        device: 0.1
      };
      
      let overallAnomalyScore = 0;
      let totalWeight = 0;
      
      for (const [key, score] of Object.entries(anomalyScores)) {
        overallAnomalyScore += score * weights[key];
        totalWeight += weights[key];
      }
      
      overallAnomalyScore = totalWeight > 0 ? overallAnomalyScore / totalWeight : 0;
      
      // 4. Determine risk level based on anomaly score
      const riskLevel = this.determineRiskLevel(overallAnomalyScore);
      
      // 5. If risk level warrants an alert, create one
      if (riskLevel !== RiskLevel.NONE) {
        const alert = this.createSecurityAlert(
          transaction.userId,
          transaction.vaultId,
          transaction.transactionId,
          transaction.ipAddress,
          riskLevel,
          `Anomalous transaction detected with score ${overallAnomalyScore.toFixed(2)}`,
          'Behavioral Analysis',
          this.determineRecommendedAction(riskLevel),
          1 - pattern.confidenceScore, // False positive probability
          {
            anomalyScores,
            overallScore: overallAnomalyScore,
            transactionType: transaction.type
          }
        );
        
        // Store the alert
        this.alerts.push(alert);
        
        // Log the alert
        this.logger.warn(`Security alert generated: ${alert.description} (${alert.riskLevel})`);
        
        return alert;
      }
      
      // 6. If in learning mode, update the user's behavioral pattern
      if (this.config.learningMode) {
        await this.updateBehavioralPattern(pattern, transaction);
      }
      
      this.logger.debug(`Transaction analysis complete: Risk level ${riskLevel}`);
      return null;
    } catch (error) {
      this.logger.error(`Failed to analyze transaction ${transaction.transactionId}`, error);
      return null;
    }
  }
  
  /**
   * Get a user's behavioral pattern, creating one if it doesn't exist
   */
  private async getUserBehavioralPattern(userId: string): Promise<BehavioralPattern> {
    // Check if we already have a pattern for this user
    if (this.patterns.has(userId)) {
      return this.patterns.get(userId)!;
    }
    
    // Create a new pattern for the user
    const newPattern: BehavioralPattern = {
      patternId: `pattern-${userId}-${Date.now()}`,
      userId,
      transactionFrequency: 0,
      chainPreferences: [],
      accessPatterns: {
        deviceTypes: [],
        geolocations: [],
        timeRanges: [],
        browserFingerprints: []
      },
      valueDistribution: {
        average: 0,
        max: 0,
        min: 0,
        stdDev: 0
      },
      commonBeneficiaries: [],
      lastAnalyzed: Date.now(),
      confidenceScore: 0.1 // Initial confidence is low
    };
    
    // Store the new pattern
    this.patterns.set(userId, newPattern);
    
    return newPattern;
  }
  
  /**
   * Update a user's behavioral pattern with new transaction data
   */
  private async updateBehavioralPattern(
    pattern: BehavioralPattern,
    transaction: {
      transactionId: string;
      userId: string;
      vaultId?: string;
      type: TransactionType;
      amount?: number;
      blockchain: BlockchainType;
      timestamp: number;
      ipAddress: string;
      deviceInfo: Record<string, any>;
      geolocation?: string;
    }
  ): Promise<BehavioralPattern> {
    // In a real implementation, this would update the pattern with sophisticated
    // statistical analysis and machine learning techniques
    
    // For this implementation, we'll do a simple update
    
    // Update chain preferences if this chain isn't already in the list
    if (!pattern.chainPreferences.includes(transaction.blockchain)) {
      pattern.chainPreferences.push(transaction.blockchain);
    }
    
    // Update geolocation if provided and not already in the list
    if (transaction.geolocation && !pattern.accessPatterns.geolocations.includes(transaction.geolocation)) {
      pattern.accessPatterns.geolocations.push(transaction.geolocation);
    }
    
    // Update device type if not already in the list
    const deviceType = transaction.deviceInfo.type || 'unknown';
    if (!pattern.accessPatterns.deviceTypes.includes(deviceType)) {
      pattern.accessPatterns.deviceTypes.push(deviceType);
    }
    
    // Update value distribution if amount is provided
    if (transaction.amount !== undefined && transaction.amount > 0) {
      // Simple running average calculation
      const oldAvg = pattern.valueDistribution.average;
      const n = pattern.accessPatterns.deviceTypes.length; // Using this as a counter of transactions
      
      pattern.valueDistribution.average = (oldAvg * n + transaction.amount) / (n + 1);
      pattern.valueDistribution.max = Math.max(pattern.valueDistribution.max, transaction.amount);
      pattern.valueDistribution.min = pattern.valueDistribution.min === 0 
        ? transaction.amount 
        : Math.min(pattern.valueDistribution.min, transaction.amount);
        
      // Simple standard deviation calculation would be here in a real implementation
    }
    
    // Update last analyzed timestamp
    pattern.lastAnalyzed = Date.now();
    
    // Increase confidence score (up to a maximum of 0.95)
    pattern.confidenceScore = Math.min(0.95, pattern.confidenceScore + 0.02);
    
    // Store the updated pattern
    this.patterns.set(pattern.userId, pattern);
    
    return pattern;
  }
  
  /**
   * Calculate how anomalous a transaction value is compared to the user's pattern
   */
  private calculateValueAnomaly(value: number, pattern: BehavioralPattern): number {
    if (value === 0 || pattern.valueDistribution.average === 0) {
      return 0; // Not enough data to determine anomaly
    }
    
    // Calculate z-score (simplified)
    const zScore = Math.abs(value - pattern.valueDistribution.average) / 
      (pattern.valueDistribution.stdDev || pattern.valueDistribution.average * 0.1); // Fallback if stdDev is 0
      
    // Normalize to 0-1 range
    return Math.min(1, zScore / 3);
  }
  
  /**
   * Calculate how anomalous a transaction frequency is
   */
  private calculateFrequencyAnomaly(timestamp: number, pattern: BehavioralPattern): number {
    if (pattern.lastAnalyzed === 0) {
      return 0; // No previous transactions
    }
    
    // Calculate time since last transaction in hours
    const hoursSinceLastTx = (timestamp - pattern.lastAnalyzed) / (1000 * 60 * 60);
    
    // Convert pattern frequency from per day to per hour
    const expectedHoursBetweenTx = pattern.transactionFrequency > 0 
      ? 24 / pattern.transactionFrequency 
      : 24; // Default to 1 per day
      
    // Calculate anomaly score based on difference between actual and expected frequency
    const ratio = hoursSinceLastTx / expectedHoursBetweenTx;
    
    // If ratio is very small (transaction is much sooner than expected)
    if (ratio < 0.1) {
      return 0.8; // High anomaly
    }
    
    // If ratio is very large (transaction is much later than expected)
    if (ratio > 10) {
      return 0.3; // Moderate anomaly
    }
    
    // For ratios between 0.5 and 2 (transaction timing is roughly as expected)
    if (ratio >= 0.5 && ratio <= 2) {
      return 0;
    }
    
    // Linear interpolation for other cases
    if (ratio < 0.5) {
      return 0.8 * (1 - ratio / 0.5); // Between 0.1 and 0.5
    } else {
      return 0.3 * ((ratio - 2) / 8); // Between 2 and 10
    }
  }
  
  /**
   * Calculate how anomalous a geolocation is
   */
  private calculateGeolocationAnomaly(geolocation: string, pattern: BehavioralPattern): number {
    if (!geolocation || pattern.accessPatterns.geolocations.length === 0) {
      return 0.5; // Moderate anomaly if no data
    }
    
    // Check if this exact geolocation has been seen before
    if (pattern.accessPatterns.geolocations.includes(geolocation)) {
      return 0; // No anomaly
    }
    
    // In a real implementation, we would calculate distance between geolocations
    // and determine anomaly based on proximity to known locations
    // For simplicity, we'll return a high anomaly for any new location
    return 0.85;
  }
  
  /**
   * Calculate how anomalous a blockchain choice is
   */
  private calculateBlockchainAnomaly(blockchain: BlockchainType, pattern: BehavioralPattern): number {
    if (pattern.chainPreferences.length === 0) {
      return 0.3; // Moderate anomaly if no data
    }
    
    // Check if this blockchain has been used before
    if (pattern.chainPreferences.includes(blockchain)) {
      return 0; // No anomaly
    }
    
    // New blockchain is moderately suspicious
    return 0.6;
  }
  
  /**
   * Calculate how anomalous a device is
   */
  private calculateDeviceAnomaly(deviceInfo: Record<string, any>, pattern: BehavioralPattern): number {
    if (!deviceInfo || pattern.accessPatterns.deviceTypes.length === 0) {
      return 0.5; // Moderate anomaly if no data
    }
    
    // Check if this device type has been seen before
    const deviceType = deviceInfo.type || 'unknown';
    if (pattern.accessPatterns.deviceTypes.includes(deviceType)) {
      return 0; // No anomaly
    }
    
    // In a real implementation, we would analyze browser fingerprints and other device characteristics
    // For simplicity, we'll return a high anomaly for any new device
    return 0.75;
  }
  
  /**
   * Determine risk level based on anomaly score
   */
  private determineRiskLevel(anomalyScore: number): RiskLevel {
    if (anomalyScore < this.config.alertThresholds.low) {
      return RiskLevel.NONE;
    } else if (anomalyScore < this.config.alertThresholds.medium) {
      return RiskLevel.LOW;
    } else if (anomalyScore < this.config.alertThresholds.high) {
      return RiskLevel.MEDIUM;
    } else if (anomalyScore < this.config.alertThresholds.critical) {
      return RiskLevel.HIGH;
    } else {
      return RiskLevel.CRITICAL;
    }
  }
  
  /**
   * Determine recommended action based on risk level
   */
  private determineRecommendedAction(riskLevel: RiskLevel): SecurityAction {
    switch (riskLevel) {
      case RiskLevel.LOW:
        return SecurityAction.MONITOR;
      case RiskLevel.MEDIUM:
        return SecurityAction.ALERT;
      case RiskLevel.HIGH:
        return SecurityAction.CHALLENGE;
      case RiskLevel.CRITICAL:
        return SecurityAction.BLOCK;
      default:
        return SecurityAction.MONITOR;
    }
  }
  
  /**
   * Create a security alert
   */
  private createSecurityAlert(
    userId: string,
    vaultId: string | undefined,
    transactionId: string,
    ipAddress: string,
    riskLevel: RiskLevel,
    description: string,
    detectionMethod: string,
    recommendedAction: SecurityAction,
    falsePositiveProbability: number,
    metadata: Record<string, any>
  ): SecurityAlert {
    // Generate a unique ID for the alert
    const alertId = createHash('sha256')
      .update(`${userId}:${transactionId}:${Date.now()}`)
      .digest('hex');
      
    return {
      id: alertId,
      timestamp: Date.now(),
      userId,
      vaultId,
      transactionId,
      ipAddress,
      riskLevel,
      description,
      detectionMethod,
      recommendedAction,
      falsePositiveProbability,
      metadata
    };
  }
  
  /**
   * Get all security alerts for a user
   */
  getAlertsForUser(userId: string): SecurityAlert[] {
    return this.alerts.filter(alert => alert.userId === userId);
  }
  
  /**
   * Get all security alerts for a vault
   */
  getAlertsForVault(vaultId: string): SecurityAlert[] {
    return this.alerts.filter(alert => alert.vaultId === vaultId);
  }
  
  /**
   * Get all security alerts by risk level
   */
  getAlertsByRiskLevel(riskLevel: RiskLevel): SecurityAlert[] {
    return this.alerts.filter(alert => alert.riskLevel === riskLevel);
  }
}

// Export a singleton instance for use throughout the application
export const behavioralAnalysisSystem = new BehavioralAnalysisSystem();
