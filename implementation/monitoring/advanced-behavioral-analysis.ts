/**
 * Advanced Behavioral Analysis System
 * 
 * A sophisticated system for detecting suspicious user behaviors, unusual transaction patterns,
 * and potential security threats using advanced AI-powered analysis.
 */

import { createHash } from 'crypto';
import { 
  RiskLevel, 
  SecurityAction, 
  SecurityAlert, 
  BehavioralPattern 
} from './behavioral-analysis-system';
import { securityLogger } from '../monitoring/security-logger';
import { BlockchainType } from '../../shared/types';

// Define the behavioral anomaly types
export enum AnomalyType {
  UNUSUAL_ACCESS_LOCATION = 'UNUSUAL_ACCESS_LOCATION',
  UNUSUAL_ACCESS_TIME = 'UNUSUAL_ACCESS_TIME',
  UNUSUAL_TRANSACTION_VOLUME = 'UNUSUAL_TRANSACTION_VOLUME',
  UNUSUAL_TRANSACTION_FREQUENCY = 'UNUSUAL_TRANSACTION_FREQUENCY',
  UNUSUAL_TRANSACTION_CHAIN = 'UNUSUAL_TRANSACTION_CHAIN',
  SUSPICIOUS_IP_ADDRESS = 'SUSPICIOUS_IP_ADDRESS',
  MULTIPLE_FAILED_ATTEMPTS = 'MULTIPLE_FAILED_ATTEMPTS',
  CROSS_CHAIN_PATTERN_DEVIATION = 'CROSS_CHAIN_PATTERN_DEVIATION',
  RAPID_GEOLOCATION_CHANGES = 'RAPID_GEOLOCATION_CHANGES',
  VAULT_ACCESS_PATTERN_DEVIATION = 'VAULT_ACCESS_PATTERN_DEVIATION'
}

// Anomaly detection sensitivity configuration
interface AnomalySensitivity {
  anomalyType: AnomalyType;
  baselineDeviationThreshold: number; // How much deviation from baseline triggers detection
  falsePositiveTolerance: number;     // How likely we are to accept false positives (0-1)
  severity: number;                    // How severe this anomaly is (0-10)
  requiredDataPoints: number;         // How many data points needed for reliable detection
}

// Behavioral analysis configuration
interface BehavioralAnalysisConfig {
  enableRealTimeMonitoring: boolean;
  sensitivityLevels: AnomalySensitivity[];
  minimumTrainingDataPoints: number;
  adaptiveBaseline: boolean;
  trackingWindowDays: number;
  highRiskActionThreshold: number;
  criticalRiskActionThreshold: number;
}

// Default configuration
const DEFAULT_CONFIG: BehavioralAnalysisConfig = {
  enableRealTimeMonitoring: true,
  sensitivityLevels: [
    {
      anomalyType: AnomalyType.UNUSUAL_ACCESS_LOCATION,
      baselineDeviationThreshold: 0.85,
      falsePositiveTolerance: 0.05,
      severity: 7,
      requiredDataPoints: 5
    },
    {
      anomalyType: AnomalyType.UNUSUAL_ACCESS_TIME,
      baselineDeviationThreshold: 0.80,
      falsePositiveTolerance: 0.10,
      severity: 4,
      requiredDataPoints: 7
    },
    {
      anomalyType: AnomalyType.UNUSUAL_TRANSACTION_VOLUME,
      baselineDeviationThreshold: 0.90,
      falsePositiveTolerance: 0.03,
      severity: 8,
      requiredDataPoints: 3
    },
    {
      anomalyType: AnomalyType.CROSS_CHAIN_PATTERN_DEVIATION,
      baselineDeviationThreshold: 0.85,
      falsePositiveTolerance: 0.04,
      severity: 7,
      requiredDataPoints: 5
    },
    {
      anomalyType: AnomalyType.VAULT_ACCESS_PATTERN_DEVIATION,
      baselineDeviationThreshold: 0.90,
      falsePositiveTolerance: 0.05,
      severity: 9,
      requiredDataPoints: 4
    }
  ],
  minimumTrainingDataPoints: 10,
  adaptiveBaseline: true,
  trackingWindowDays: 90,
  highRiskActionThreshold: 7,
  criticalRiskActionThreshold: 9
};

// Transaction context for analysis
export interface TransactionContext {
  userId: string;
  vaultId?: string;
  transactionId?: string;
  timestamp: number;
  chainType: BlockchainType;
  amount?: number;
  transactionType: string;
  sourceAddress: string;
  destinationAddress: string;
  ipAddress: string;
  geolocation?: {
    country: string;
    city?: string;
    coordinates?: [number, number]; // [latitude, longitude]
  };
  deviceInfo?: {
    type: string;
    fingerprint: string;
    userAgent: string;
  };
  metadata: Record<string, any>;
}

// Access context for analysis
export interface AccessContext {
  userId: string;
  timestamp: number;
  vaultId?: string;
  actionType: string;
  ipAddress: string;
  geolocation?: {
    country: string;
    city?: string;
    coordinates?: [number, number]; // [latitude, longitude]
  };
  deviceInfo?: {
    type: string;
    fingerprint: string;
    userAgent: string;
  };
  metadata: Record<string, any>;
}

/**
 * Advanced Behavioral Analysis System
 * 
 * Implements sophisticated AI-based analysis of user behavior to detect
 * potential security threats and fraudulent activities.
 */
class AdvancedBehavioralAnalysis {
  private config: BehavioralAnalysisConfig;
  private userPatterns: Map<string, BehavioralPattern> = new Map();
  private alerts: SecurityAlert[] = [];
  private ipReputationDatabase: Map<string, { risk: number, reason: string }> = new Map();
  private geoVelocityTracking: Map<string, Array<{ time: number, coordinates: [number, number] }>> = new Map();
  
  constructor(config: Partial<BehavioralAnalysisConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    securityLogger.info('Advanced Behavioral Analysis System initialized', { config: this.config });
    
    // In a real implementation, we would load user patterns from a database
    // and populate the IP reputation database from external sources
  }
  
  /**
   * Analyze a transaction for suspicious patterns and anomalies
   */
  async analyzeTransaction(context: TransactionContext): Promise<SecurityAlert | null> {
    try {
      securityLogger.debug(`Analyzing transaction for user ${context.userId}`, {
        transactionId: context.transactionId,
        chain: context.chainType
      });
      
      // Get or initialize user pattern
      let userPattern = this.userPatterns.get(context.userId);
      if (!userPattern) {
        userPattern = this.initializeUserPattern(context.userId);
        this.userPatterns.set(context.userId, userPattern);
      }
      
      // Check for IP address reputation
      const ipRisk = await this.checkIpReputation(context.ipAddress);
      if (ipRisk.risk > 0.7) {
        return this.createAlert(
          context.userId,
          context.vaultId,
          context.transactionId,
          RiskLevel.HIGH,
          `Suspicious IP address: ${ipRisk.reason}`,
          AnomalyType.SUSPICIOUS_IP_ADDRESS,
          SecurityAction.CHALLENGE,
          0.9,
          {
            ipAddress: context.ipAddress,
            riskScore: ipRisk.risk,
            reason: ipRisk.reason
          }
        );
      }
      
      // Track geo-velocity (impossible travel detection)
      if (context.geolocation?.coordinates) {
        const geoAnomaly = this.checkGeoVelocityAnomaly(
          context.userId, 
          context.timestamp, 
          context.geolocation.coordinates
        );
        
        if (geoAnomaly) {
          return this.createAlert(
            context.userId,
            context.vaultId,
            context.transactionId,
            RiskLevel.HIGH,
            `Suspicious geolocation change detected`,
            AnomalyType.RAPID_GEOLOCATION_CHANGES,
            SecurityAction.CHALLENGE,
            0.85,
            {
              currentLocation: context.geolocation,
              previousLocations: this.geoVelocityTracking.get(context.userId),
              impossibleTravel: true
            }
          );
        }
      }
      
      // Run multiple anomaly checks in parallel
      const anomalyChecks = await Promise.all([
        this.checkTransactionVolumeAnomaly(context, userPattern),
        this.checkAccessTimeAnomaly(context, userPattern),
        this.checkBlockchainPatternAnomaly(context, userPattern)
      ]);
      
      // Find the most severe anomaly (if any)
      const detectedAnomalies = anomalyChecks.filter(check => check !== null);
      if (detectedAnomalies.length > 0) {
        // Sort by risk level severity
        detectedAnomalies.sort((a, b) => {
          const riskLevels = {
            [RiskLevel.CRITICAL]: 4,
            [RiskLevel.HIGH]: 3,
            [RiskLevel.MEDIUM]: 2,
            [RiskLevel.LOW]: 1,
            [RiskLevel.NONE]: 0
          };
          return riskLevels[b.riskLevel] - riskLevels[a.riskLevel];
        });
        
        const alert = detectedAnomalies[0];
        this.alerts.push(alert);
        return alert;
      }
      
      // Update user behavioral pattern with this legitimate transaction
      this.updateUserPattern(userPattern, context);
      
      // No anomalies detected
      return null;
    } catch (error) {
      securityLogger.error(`Error in transaction behavioral analysis`, { 
        userId: context.userId,
        error 
      });
      return null;
    }
  }
  
  /**
   * Analyze a user access event for suspicious patterns
   */
  async analyzeAccess(context: AccessContext): Promise<SecurityAlert | null> {
    try {
      securityLogger.debug(`Analyzing access for user ${context.userId}`, {
        actionType: context.actionType
      });
      
      // Get or initialize user pattern
      let userPattern = this.userPatterns.get(context.userId);
      if (!userPattern) {
        userPattern = this.initializeUserPattern(context.userId);
        this.userPatterns.set(context.userId, userPattern);
      }
      
      // Check for IP reputation
      const ipRisk = await this.checkIpReputation(context.ipAddress);
      if (ipRisk.risk > 0.7) {
        return this.createAlert(
          context.userId,
          context.vaultId,
          undefined,
          RiskLevel.HIGH,
          `Suspicious IP address during access: ${ipRisk.reason}`,
          AnomalyType.SUSPICIOUS_IP_ADDRESS,
          SecurityAction.CHALLENGE,
          0.9,
          {
            ipAddress: context.ipAddress,
            riskScore: ipRisk.risk,
            reason: ipRisk.reason,
            actionType: context.actionType
          }
        );
      }
      
      // Track geo-velocity (impossible travel detection)
      if (context.geolocation?.coordinates) {
        const geoAnomaly = this.checkGeoVelocityAnomaly(
          context.userId, 
          context.timestamp, 
          context.geolocation.coordinates
        );
        
        if (geoAnomaly) {
          return this.createAlert(
            context.userId,
            context.vaultId,
            undefined,
            RiskLevel.HIGH,
            `Suspicious geolocation change detected during access`,
            AnomalyType.RAPID_GEOLOCATION_CHANGES,
            SecurityAction.CHALLENGE,
            0.85,
            {
              currentLocation: context.geolocation,
              previousLocations: this.geoVelocityTracking.get(context.userId),
              impossibleTravel: true,
              actionType: context.actionType
            }
          );
        }
      }
      
      // Run access-specific anomaly checks
      const locationAnomaly = this.checkAccessLocationAnomaly(context, userPattern);
      const timeAnomaly = this.checkAccessTimeAnomaly(context, userPattern);
      
      // Return the more severe anomaly if either exists
      if (locationAnomaly && timeAnomaly) {
        const riskLevels = {
          [RiskLevel.CRITICAL]: 4,
          [RiskLevel.HIGH]: 3,
          [RiskLevel.MEDIUM]: 2,
          [RiskLevel.LOW]: 1,
          [RiskLevel.NONE]: 0
        };
        
        const alert = riskLevels[locationAnomaly.riskLevel] >= riskLevels[timeAnomaly.riskLevel] 
          ? locationAnomaly 
          : timeAnomaly;
          
        this.alerts.push(alert);
        return alert;
      } else if (locationAnomaly) {
        this.alerts.push(locationAnomaly);
        return locationAnomaly;
      } else if (timeAnomaly) {
        this.alerts.push(timeAnomaly);
        return timeAnomaly;
      }
      
      // Update user behavioral pattern with this legitimate access
      this.updateUserAccessPattern(userPattern, context);
      
      // No anomalies detected
      return null;
    } catch (error) {
      securityLogger.error(`Error in access behavioral analysis`, { 
        userId: context.userId,
        error 
      });
      return null;
    }
  }
  
  /**
   * Check if a transaction volume is anomalous compared to user's history
   */
  private async checkTransactionVolumeAnomaly(
    context: TransactionContext, 
    userPattern: BehavioralPattern
  ): Promise<SecurityAlert | null> {
    // Skip if amount is not provided or if we don't have enough data
    if (!context.amount || !userPattern.transactionVolume) {
      return null;
    }
    
    // Find the sensitivity configuration for this anomaly type
    const sensitivityConfig = this.config.sensitivityLevels.find(
      s => s.anomalyType === AnomalyType.UNUSUAL_TRANSACTION_VOLUME
    );
    
    if (!sensitivityConfig) {
      return null;
    }
    
    // Skip if we don't have enough data points yet
    if (userPattern.transactionCount < sensitivityConfig.requiredDataPoints) {
      return null;
    }
    
    // Calculate how much this transaction deviates from the user's average
    const avgVolume = userPattern.transactionVolume / userPattern.transactionCount;
    const normalizedDeviation = context.amount / avgVolume;
    
    // If transaction is much larger than usual (above threshold)
    if (normalizedDeviation > sensitivityConfig.baselineDeviationThreshold + 1) {
      // Calculate risk based on how much larger it is
      const deviationFactor = Math.min((normalizedDeviation - 1) / 10, 1);
      const riskFactor = deviationFactor * sensitivityConfig.severity / 10;
      
      // Determine risk level
      let riskLevel = RiskLevel.LOW;
      if (riskFactor > 0.8) {
        riskLevel = RiskLevel.CRITICAL;
      } else if (riskFactor > 0.6) {
        riskLevel = RiskLevel.HIGH;
      } else if (riskFactor > 0.3) {
        riskLevel = RiskLevel.MEDIUM;
      }
      
      // Determine action based on risk
      let action = SecurityAction.MONITOR;
      if (riskLevel === RiskLevel.CRITICAL) {
        action = SecurityAction.BLOCK;
      } else if (riskLevel === RiskLevel.HIGH) {
        action = SecurityAction.CHALLENGE;
      } else if (riskLevel === RiskLevel.MEDIUM) {
        action = SecurityAction.ALERT;
      }
      
      return this.createAlert(
        context.userId,
        context.vaultId,
        context.transactionId,
        riskLevel,
        `Unusual transaction volume detected`,
        AnomalyType.UNUSUAL_TRANSACTION_VOLUME,
        action,
        1 - sensitivityConfig.falsePositiveTolerance,
        {
          amount: context.amount,
          averageAmount: avgVolume,
          deviationFactor: normalizedDeviation,
          chain: context.chainType
        }
      );
    }
    
    return null;
  }
  
  /**
   * Check for blockchain usage pattern anomalies
   */
  private async checkBlockchainPatternAnomaly(
    context: TransactionContext, 
    userPattern: BehavioralPattern
  ): Promise<SecurityAlert | null> {
    // Skip if we don't have chain preferences data
    if (!userPattern.chainPreferences || userPattern.chainPreferences.length === 0) {
      return null;
    }
    
    // Find the sensitivity configuration for this anomaly type
    const sensitivityConfig = this.config.sensitivityLevels.find(
      s => s.anomalyType === AnomalyType.CROSS_CHAIN_PATTERN_DEVIATION
    );
    
    if (!sensitivityConfig) {
      return null;
    }
    
    // Skip if we don't have enough data points yet
    if (userPattern.transactionCount < sensitivityConfig.requiredDataPoints) {
      return null;
    }
    
    // Check if user has used this chain before
    const hasUsedChain = userPattern.chainPreferences.includes(context.chainType);
    
    // If this is an unusual chain for this user
    if (!hasUsedChain) {
      return this.createAlert(
        context.userId,
        context.vaultId,
        context.transactionId,
        RiskLevel.MEDIUM,
        `Unusual blockchain network usage detected`,
        AnomalyType.UNUSUAL_TRANSACTION_CHAIN,
        SecurityAction.ALERT,
        0.75,
        {
          currentChain: context.chainType,
          usualChains: userPattern.chainPreferences,
          transactionType: context.transactionType
        }
      );
    }
    
    return null;
  }
  
  /**
   * Check for access time anomalies
   */
  private checkAccessTimeAnomaly(
    context: AccessContext | TransactionContext, 
    userPattern: BehavioralPattern
  ): SecurityAlert | null {
    if (!userPattern.accessPatterns || !userPattern.accessPatterns.timeRanges) {
      return null;
    }
    
    // Get the hour of the day from the timestamp
    const date = new Date(context.timestamp);
    const hourOfDay = date.getUTCHours();
    
    // Parse the user's usual hours
    const usualHours: number[] = [];
    userPattern.accessPatterns.timeRanges.forEach(timeRange => {
      const [start, end] = timeRange.split('-').map(t => parseInt(t));
      for (let h = start; h <= end; h++) {
        usualHours.push(h % 24); // Handle ranges that cross midnight
      }
    });
    
    // If this hour is unusual for this user
    if (!usualHours.includes(hourOfDay)) {
      // Calculate how far outside the usual range it is
      const closestHour = usualHours.reduce((closest, hour) => {
        const distance = Math.min(
          Math.abs(hour - hourOfDay), 
          Math.abs(hour - hourOfDay + 24), 
          Math.abs(hour - hourOfDay - 24)
        );
        return distance < closest.distance ? { hour, distance } : closest;
      }, { hour: -1, distance: 24 });
      
      const deviation = closestHour.distance / 12; // Normalize to 0-1 (max dist is 12h)
      const riskFactor = Math.min(deviation, 1);
      
      // Determine risk level
      let riskLevel = RiskLevel.LOW;
      if (riskFactor > 0.7) {
        riskLevel = RiskLevel.HIGH;
      } else if (riskFactor > 0.4) {
        riskLevel = RiskLevel.MEDIUM;
      }
      
      return this.createAlert(
        context.userId,
        'vaultId' in context ? context.vaultId : undefined,
        'transactionId' in context ? context.transactionId : undefined,
        riskLevel,
        `Unusual access time detected`,
        AnomalyType.UNUSUAL_ACCESS_TIME,
        riskLevel === RiskLevel.HIGH ? SecurityAction.CHALLENGE : SecurityAction.ALERT,
        0.8,
        {
          currentHour: hourOfDay,
          usualHours,
          deviationHours: closestHour.distance
        }
      );
    }
    
    return null;
  }
  
  /**
   * Check for access location anomalies
   */
  private checkAccessLocationAnomaly(
    context: AccessContext, 
    userPattern: BehavioralPattern
  ): SecurityAlert | null {
    if (!context.geolocation || !userPattern.accessPatterns || !userPattern.accessPatterns.geolocations) {
      return null;
    }
    
    // Check if this location is in the user's usual locations
    const hasUsedLocation = userPattern.accessPatterns.geolocations.includes(
      context.geolocation.country
    );
    
    // If this is an unusual location for this user
    if (!hasUsedLocation) {
      return this.createAlert(
        context.userId,
        context.vaultId,
        undefined,
        RiskLevel.HIGH,
        `Unusual access location detected`,
        AnomalyType.UNUSUAL_ACCESS_LOCATION,
        SecurityAction.CHALLENGE,
        0.9,
        {
          currentLocation: context.geolocation,
          usualLocations: userPattern.accessPatterns.geolocations
        }
      );
    }
    
    return null;
  }
  
  /**
   * Check for impossible travel (rapid geolocation changes)
   */
  private checkGeoVelocityAnomaly(
    userId: string,
    timestamp: number,
    coordinates: [number, number]
  ): boolean {
    // Get user's location history
    const locationHistory = this.geoVelocityTracking.get(userId) || [];
    
    // Update tracking first (for next time)
    this.geoVelocityTracking.set(userId, [
      ...locationHistory.slice(-9), // Keep last 9 entries
      { time: timestamp, coordinates }
    ]);
    
    // If no previous locations, no anomaly
    if (locationHistory.length === 0) {
      return false;
    }
    
    // Get last location
    const lastLocation = locationHistory[locationHistory.length - 1];
    
    // Calculate time difference in hours
    const timeDiffHours = (timestamp - lastLocation.time) / (1000 * 60 * 60);
    
    // Calculate distance in kilometers using Haversine formula
    const distance = this.calculateDistance(
      lastLocation.coordinates[0], lastLocation.coordinates[1],
      coordinates[0], coordinates[1]
    );
    
    // Calculate speed in km/h
    const speed = distance / timeDiffHours;
    
    // If speed is greater than 1000 km/h (faster than commercial flight)
    // and the distance is significant (more than 500km)
    if (speed > 1000 && distance > 500) {
      securityLogger.warn(`Impossible travel detected for user ${userId}`, {
        speed: `${speed.toFixed(2)} km/h`,
        distance: `${distance.toFixed(2)} km`,
        timeDiff: `${timeDiffHours.toFixed(2)} hours`
      });
      return true;
    }
    
    return false;
  }
  
  /**
   * Calculate the great-circle distance between two points using Haversine formula
   * Returns distance in kilometers
   */
  private calculateDistance(
    lat1: number, lon1: number, 
    lat2: number, lon2: number
  ): number {
    const R = 6371; // Earth's radius in km
    const dLat = this.deg2rad(lat2 - lat1);
    const dLon = this.deg2rad(lon2 - lon1);
    
    const a = 
      Math.sin(dLat/2) * Math.sin(dLat/2) +
      Math.cos(this.deg2rad(lat1)) * Math.cos(this.deg2rad(lat2)) * 
      Math.sin(dLon/2) * Math.sin(dLon/2);
      
    const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
    return R * c;
  }
  
  private deg2rad(deg: number): number {
    return deg * (Math.PI/180);
  }
  
  /**
   * Check IP address reputation
   * In a real implementation, this would query reputation databases
   */
  private async checkIpReputation(ipAddress: string): Promise<{ risk: number, reason: string }> {
    // First check our cached results
    if (this.ipReputationDatabase.has(ipAddress)) {
      return this.ipReputationDatabase.get(ipAddress);
    }
    
    // Simulate checking against reputation databases
    // In production this would call real IP reputation APIs
    
    // Create deterministic but pseudo-random risk for demo purposes
    const hash = createHash('sha256').update(ipAddress).digest('hex');
    const hashNum = parseInt(hash.slice(0, 8), 16);
    const risk = (hashNum % 100) / 100; // 0-1 risk factor
    
    let reason = 'No risk factors detected';
    if (risk > 0.97) {
      reason = 'Known malicious activity';
    } else if (risk > 0.9) {
      reason = 'Suspicious activity reported';
    } else if (risk > 0.8) {
      reason = 'Tor exit node';
    } else if (risk > 0.7) {
      reason = 'Anonymous proxy';
    }
    
    // Cache the result
    const result = { risk, reason };
    this.ipReputationDatabase.set(ipAddress, result);
    
    return result;
  }
  
  /**
   * Initialize a new user behavioral pattern
   */
  private initializeUserPattern(userId: string): BehavioralPattern {
    return {
      patternId: `pattern-${userId}-${Date.now()}`,
      userId,
      transactionFrequency: 0,
      chainPreferences: [],
      accessPatterns: {
        deviceTypes: [],
        geolocations: [],
        timeRanges: []
      },
      transactionVolume: 0,
      transactionCount: 0,
      lastUpdated: Date.now()
    };
  }
  
  /**
   * Update user pattern with new transaction data
   */
  private updateUserPattern(pattern: BehavioralPattern, context: TransactionContext): void {
    // Update chain preferences
    if (!pattern.chainPreferences.includes(context.chainType)) {
      pattern.chainPreferences.push(context.chainType);
    }
    
    // Update transaction volume and count
    if (context.amount !== undefined) {
      pattern.transactionVolume = (pattern.transactionVolume || 0) + context.amount;
      pattern.transactionCount = (pattern.transactionCount || 0) + 1;
    }
    
    // Update transaction frequency (avg transactions per day)
    const daysSinceFirstTx = (Date.now() - pattern.lastUpdated) / (1000 * 60 * 60 * 24) + 1;
    pattern.transactionFrequency = pattern.transactionCount / daysSinceFirstTx;
    
    // Update access patterns
    this.updateAccessPatterns(pattern, context);
    
    // Update timestamp
    pattern.lastUpdated = Date.now();
  }
  
  /**
   * Update user access patterns
   */
  private updateUserAccessPattern(pattern: BehavioralPattern, context: AccessContext): void {
    this.updateAccessPatterns(pattern, context);
    pattern.lastUpdated = Date.now();
  }
  
  /**
   * Update access patterns from any context
   */
  private updateAccessPatterns(pattern: BehavioralPattern, context: AccessContext | TransactionContext): void {
    // Initialize access patterns if needed
    pattern.accessPatterns = pattern.accessPatterns || {
      deviceTypes: [],
      geolocations: [],
      timeRanges: []
    };
    
    // Update device types
    if (context.deviceInfo?.type && !pattern.accessPatterns.deviceTypes.includes(context.deviceInfo.type)) {
      pattern.accessPatterns.deviceTypes.push(context.deviceInfo.type);
    }
    
    // Update geolocations
    if (context.geolocation?.country && !pattern.accessPatterns.geolocations.includes(context.geolocation.country)) {
      pattern.accessPatterns.geolocations.push(context.geolocation.country);
    }
    
    // Update time ranges
    const date = new Date(context.timestamp);
    const hour = date.getUTCHours();
    
    // Check if this hour fits into an existing time range
    let foundRange = false;
    const updatedRanges: string[] = [];
    
    for (const range of pattern.accessPatterns.timeRanges) {
      const [start, end] = range.split('-').map(t => parseInt(t));
      
      // Check if hour is within or adjacent to this range
      if (
        (hour >= start && hour <= end) || // Within range
        hour === (start - 1) || hour === (end + 1) // Adjacent to range
      ) {
        // Extend the range
        const newStart = Math.min(start, hour);
        const newEnd = Math.max(end, hour);
        updatedRanges.push(`${newStart}-${newEnd}`);
        foundRange = true;
      } else {
        // Keep the range as is
        updatedRanges.push(range);
      }
    }
    
    // If hour didn't fit into any range, add a new one
    if (!foundRange) {
      updatedRanges.push(`${hour}-${hour}`);
    }
    
    // Update the time ranges
    pattern.accessPatterns.timeRanges = updatedRanges;
  }
  
  /**
   * Create a security alert
   */
  private createAlert(
    userId: string,
    vaultId: string | undefined,
    transactionId: string | undefined,
    riskLevel: RiskLevel,
    description: string,
    detectionMethod: AnomalyType,
    recommendedAction: SecurityAction,
    falsePositiveProbability: number,
    metadata: Record<string, any>
  ): SecurityAlert {
    const alert: SecurityAlert = {
      id: `alert-${Date.now()}-${Math.random().toString(36).slice(2, 10)}`,
      timestamp: Date.now(),
      userId,
      vaultId,
      transactionId,
      riskLevel,
      description,
      detectionMethod: detectionMethod.toString(),
      recommendedAction,
      falsePositiveProbability,
      metadata
    };
    
    securityLogger.warn(`Security alert generated: ${description}`, {
      alertId: alert.id,
      userId,
      riskLevel,
      action: recommendedAction
    });
    
    return alert;
  }
  
  /**
   * Get all active alerts
   */
  getAlerts(): SecurityAlert[] {
    return this.alerts;
  }
  
  /**
   * Get alerts for a specific user
   */
  getUserAlerts(userId: string): SecurityAlert[] {
    return this.alerts.filter(alert => alert.userId === userId);
  }
  
  /**
   * Clear a specific alert (e.g., after resolution)
   */
  clearAlert(alertId: string): boolean {
    const index = this.alerts.findIndex(alert => alert.id === alertId);
    if (index >= 0) {
      this.alerts.splice(index, 1);
      return true;
    }
    return false;
  }
  
  /**
   * Get behavioral pattern for a user
   */
  getUserPattern(userId: string): BehavioralPattern | undefined {
    return this.userPatterns.get(userId);
  }
  
  /**
   * Mark an alert as a false positive to improve detection
   */
  markAlertAsFalsePositive(alertId: string): boolean {
    const alert = this.alerts.find(a => a.id === alertId);
    if (!alert) {
      return false;
    }
    
    // Find the sensitivity setting for this anomaly type
    const anomalyType = alert.detectionMethod as AnomalyType;
    const sensitivityIndex = this.config.sensitivityLevels.findIndex(
      s => s.anomalyType.toString() === anomalyType
    );
    
    if (sensitivityIndex >= 0) {
      // Adjust false positive tolerance
      this.config.sensitivityLevels[sensitivityIndex].falsePositiveTolerance += 0.05;
      this.config.sensitivityLevels[sensitivityIndex].falsePositiveTolerance = 
        Math.min(this.config.sensitivityLevels[sensitivityIndex].falsePositiveTolerance, 0.3);
        
      // Clear the alert
      return this.clearAlert(alertId);
    }
    
    return false;
  }
}

// Export singleton instance
export const advancedBehavioralAnalysis = new AdvancedBehavioralAnalysis();