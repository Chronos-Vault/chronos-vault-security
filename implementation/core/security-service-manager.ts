/**
 * Security Service Manager
 * 
 * Central security management system that integrates all security components
 * into a cohesive security architecture for maximum protection of assets.
 */

import { Request, Response, NextFunction } from 'express';
import { dataPersistenceService } from './data-persistence-service';
import { zeroKnowledgeShield } from './zero-knowledge-shield';
import { quantumResistantEncryption } from './quantum-resistant-encryption';
import { behavioralAnalysisSystem, RiskLevel, SecurityAction } from './behavioral-analysis-system';
import { multiSignatureGateway, ApprovalStatus } from './multi-signature-gateway';

interface SecurityMetrics {
  totalIncidents: number;
  riskLevelDistribution: Record<string, number>;
  averageResponseTimeMs: number;
  blockedAttackCount: number;
  challengedTransactionCount: number;
  falsePositiveRate: number;
  overallHealthScore: number;
  lastUpdated: number;
}

export enum SecurityFeature {
  ZERO_KNOWLEDGE_PRIVACY = 'ZERO_KNOWLEDGE_PRIVACY',
  QUANTUM_RESISTANT_ENCRYPTION = 'QUANTUM_RESISTANT_ENCRYPTION',
  BEHAVIORAL_ANALYSIS = 'BEHAVIORAL_ANALYSIS',
  MULTI_SIGNATURE = 'MULTI_SIGNATURE',
  DATA_PERSISTENCE = 'DATA_PERSISTENCE',
  CROSS_CHAIN_VERIFICATION = 'CROSS_CHAIN_VERIFICATION'
}

export interface SecurityLevel {
  level: 'standard' | 'enhanced' | 'maximum';
  features: Record<SecurityFeature, boolean>;
  multiSigThreshold: number;
  enforceQuantumResistance: boolean;
  performBehavioralAnalysis: boolean;
  requireGeolocationVerification: boolean;
  requireHardwareKeys: boolean;
  useZeroKnowledgeProofs: boolean;
  autoBackupFrequencyHours: number;
}

const SECURITY_LEVELS: Record<string, SecurityLevel> = {
  standard: {
    level: 'standard',
    features: {
      [SecurityFeature.ZERO_KNOWLEDGE_PRIVACY]: false,
      [SecurityFeature.QUANTUM_RESISTANT_ENCRYPTION]: false,
      [SecurityFeature.BEHAVIORAL_ANALYSIS]: true,
      [SecurityFeature.MULTI_SIGNATURE]: true,
      [SecurityFeature.DATA_PERSISTENCE]: true,
      [SecurityFeature.CROSS_CHAIN_VERIFICATION]: false
    },
    multiSigThreshold: 2,
    enforceQuantumResistance: false,
    performBehavioralAnalysis: true,
    requireGeolocationVerification: false,
    requireHardwareKeys: false,
    useZeroKnowledgeProofs: false,
    autoBackupFrequencyHours: 24
  },
  enhanced: {
    level: 'enhanced',
    features: {
      [SecurityFeature.ZERO_KNOWLEDGE_PRIVACY]: true,
      [SecurityFeature.QUANTUM_RESISTANT_ENCRYPTION]: true,
      [SecurityFeature.BEHAVIORAL_ANALYSIS]: true,
      [SecurityFeature.MULTI_SIGNATURE]: true,
      [SecurityFeature.DATA_PERSISTENCE]: true,
      [SecurityFeature.CROSS_CHAIN_VERIFICATION]: true
    },
    multiSigThreshold: 3,
    enforceQuantumResistance: true,
    performBehavioralAnalysis: true,
    requireGeolocationVerification: true,
    requireHardwareKeys: false,
    useZeroKnowledgeProofs: true,
    autoBackupFrequencyHours: 12
  },
  maximum: {
    level: 'maximum',
    features: {
      [SecurityFeature.ZERO_KNOWLEDGE_PRIVACY]: true,
      [SecurityFeature.QUANTUM_RESISTANT_ENCRYPTION]: true,
      [SecurityFeature.BEHAVIORAL_ANALYSIS]: true,
      [SecurityFeature.MULTI_SIGNATURE]: true,
      [SecurityFeature.DATA_PERSISTENCE]: true,
      [SecurityFeature.CROSS_CHAIN_VERIFICATION]: true
    },
    multiSigThreshold: 4,
    enforceQuantumResistance: true,
    performBehavioralAnalysis: true,
    requireGeolocationVerification: true,
    requireHardwareKeys: true,
    useZeroKnowledgeProofs: true,
    autoBackupFrequencyHours: 6
  }
};

/**
 * Security Service Manager
 * 
 * Provides a unified interface for all security features in the platform,
 * integrating multiple security systems for comprehensive protection.
 */
export class SecurityServiceManager {
  private metrics: SecurityMetrics = {
    totalIncidents: 0,
    riskLevelDistribution: {
      [RiskLevel.LOW]: 0,
      [RiskLevel.MEDIUM]: 0,
      [RiskLevel.HIGH]: 0,
      [RiskLevel.CRITICAL]: 0
    },
    averageResponseTimeMs: 0,
    blockedAttackCount: 0,
    challengedTransactionCount: 0,
    falsePositiveRate: 0.05, // Initial estimate
    overallHealthScore: 95,  // Initial score
    lastUpdated: Date.now()
  };
  
  private featureStatus: Record<SecurityFeature, boolean> = {
    [SecurityFeature.ZERO_KNOWLEDGE_PRIVACY]: true,
    [SecurityFeature.QUANTUM_RESISTANT_ENCRYPTION]: true,
    [SecurityFeature.BEHAVIORAL_ANALYSIS]: true,
    [SecurityFeature.MULTI_SIGNATURE]: true,
    [SecurityFeature.DATA_PERSISTENCE]: true,
    [SecurityFeature.CROSS_CHAIN_VERIFICATION]: true
  };
  
  private logger: any; // Would be proper logger
  
  constructor() {
    this.logger = {
      debug: (msg: string) => console.debug(`[SecurityManager] ${msg}`),
      info: (msg: string) => console.info(`[SecurityManager] ${msg}`),
      warn: (msg: string) => console.warn(`[SecurityManager] ${msg}`),
      error: (msg: string, error?: any) => console.error(`[SecurityManager] ${msg}`, error)
    };
    
    this.logger.info('Security Service Manager initialized');
  }
  
  /**
   * Initialize all security services
   */
  async initialize(): Promise<void> {
    this.logger.info('Initializing all security services');
    
    try {
      // Initialize behavioral analysis system
      await behavioralAnalysisSystem.initialize();
      
      // Initialize data persistence service
      await dataPersistenceService.initialize();
      
      // Schedule periodic security tasks
      this.scheduleSecurityTasks();
      
      this.logger.info('All security services initialized successfully');
    } catch (error) {
      this.logger.error('Failed to initialize security services', error);
      throw new Error(`Security services initialization failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
  
  /**
   * Get the security level configuration for a vault
   */
  getSecurityLevel(level: 'standard' | 'enhanced' | 'maximum'): SecurityLevel {
    return SECURITY_LEVELS[level];
  }
  
  /**
   * Apply security settings based on a security level
   */
  async applySecurityLevel(vaultId: string, level: 'standard' | 'enhanced' | 'maximum'): Promise<void> {
    const securityLevel = this.getSecurityLevel(level);
    
    this.logger.info(`Applying ${level} security settings to vault ${vaultId}`);
    
    // Update feature status based on security level
    for (const [feature, enabled] of Object.entries(securityLevel.features)) {
      this.featureStatus[feature as SecurityFeature] = enabled;
    }
    
    // Create a system backup before making security changes
    await dataPersistenceService.createRestorePoint(`Pre-security-change-${vaultId}`);
    
    // Schedule appropriate backup frequency
    await dataPersistenceService.setBackupInterval(securityLevel.autoBackupFrequencyHours * 60 * 60 * 1000);
    
    this.logger.info(`Security level ${level} applied to vault ${vaultId}`);
  }
  
  /**
   * Create Express middleware for security checks
   */
  createSecurityMiddleware() {
    return async (req: Request, res: Response, next: NextFunction) => {
      try {
        const startTime = Date.now();
        
        // 1. Extract user information from the request
        const userId = req.session?.userId || req.body?.userId || 'unknown';
        
        // 2. Collect context information for behavioral analysis
        const transactionContext = {
          transactionId: req.id || `req-${Date.now()}-${Math.random().toString(36).substring(2, 15)}`,
          userId,
          vaultId: req.params.vaultId || req.body?.vaultId,
          type: this.mapRequestToTransactionType(req),
          amount: req.body?.amount,
          blockchain: req.body?.blockchainType,
          timestamp: Date.now(),
          ipAddress: req.ip || '0.0.0.0',
          deviceInfo: {
            type: this.extractDeviceType(req),
            userAgent: req.headers['user-agent']
          },
          geolocation: req.body?.geolocation || req.headers['x-geo-location']
        };
        
        // 3. Perform behavioral analysis if enabled
        if (this.featureStatus[SecurityFeature.BEHAVIORAL_ANALYSIS]) {
          const alert = await behavioralAnalysisSystem.analyzeTransaction(transactionContext);
          
          if (alert) {
            // Update metrics
            this.metrics.totalIncidents++;
            this.metrics.riskLevelDistribution[alert.riskLevel]++;
            
            // Handle different risk levels
            if (alert.riskLevel === RiskLevel.HIGH || alert.riskLevel === RiskLevel.CRITICAL) {
              if (alert.recommendedAction === SecurityAction.BLOCK) {
                this.metrics.blockedAttackCount++;
                return res.status(403).json({
                  error: 'Security violation detected',
                  message: 'This action has been blocked due to suspicious activity',
                  requestId: transactionContext.transactionId
                });
              } else if (alert.recommendedAction === SecurityAction.CHALLENGE) {
                this.metrics.challengedTransactionCount++;
                req.securityChallenge = true; // Flag for additional verification
              }
            }
            
            // Attach alert to request for logging/monitoring
            req.securityAlert = alert;
          }
        }
        
        // 4. Check if multi-signature is required for this operation
        if (this.featureStatus[SecurityFeature.MULTI_SIGNATURE] && this.requiresMultiSignature(req)) {
          // Check if this request includes a valid approval request ID
          const approvalRequestId = req.body?.approvalRequestId;
          
          if (!approvalRequestId) {
            return res.status(400).json({
              error: 'Multi-signature required',
              message: 'This operation requires multi-signature approval',
              requestId: transactionContext.transactionId
            });
          }
          
          // Verify the approval request
          const approvalRequest = multiSignatureGateway.getApprovalRequest(approvalRequestId);
          
          if (!approvalRequest || approvalRequest.status !== ApprovalStatus.APPROVED) {
            return res.status(403).json({
              error: 'Invalid approval request',
              message: 'The provided approval request is invalid or not approved',
              status: approvalRequest?.status || 'NOT_FOUND',
              requestId: transactionContext.transactionId
            });
          }
        }
        
        // 5. Record response time
        const responseTime = Date.now() - startTime;
        const totalResponses = this.metrics.totalIncidents;
        this.metrics.averageResponseTimeMs = (
          (this.metrics.averageResponseTimeMs * totalResponses) + responseTime
        ) / (totalResponses + 1);
        
        // Continue to the next middleware or route handler
        next();
      } catch (error) {
        this.logger.error('Error in security middleware', error);
        next(error);
      }
    };
  }
  
  /**
   * Get current security metrics
   */
  getSecurityMetrics(): SecurityMetrics {
    this.metrics.lastUpdated = Date.now();
    return { ...this.metrics };
  }
  
  /**
   * Check if a particular security feature is enabled
   */
  isFeatureEnabled(feature: SecurityFeature): boolean {
    return this.featureStatus[feature];
  }
  
  /**
   * Enable or disable a security feature
   */
  setFeatureStatus(feature: SecurityFeature, enabled: boolean): void {
    this.featureStatus[feature] = enabled;
    this.logger.info(`Security feature ${feature} set to ${enabled ? 'enabled' : 'disabled'}`);
  }
  
  /**
   * Check if an operation requires multi-signature
   */
  private requiresMultiSignature(req: Request): boolean {
    // Determine if the operation is high-risk and requires multi-signature
    // For example, any vault asset unlocking, beneficiary changes, etc.
    
    // Check the HTTP method and path
    const method = req.method.toUpperCase();
    const path = req.path;
    
    // Operations that always require multi-signature
    if (
      (method === 'POST' && path.includes('/vaults') && req.body?.unlock) ||
      (method === 'PUT' && path.includes('/vaults') && path.includes('/multisig')) ||
      (method === 'POST' && path.includes('/signature-requests')) ||
      (method === 'PUT' && path.includes('/vaults') && req.body?.beneficiaries) ||
      (method === 'POST' && path.includes('/vaults') && req.body?.amount >= 10000) // High-value vaults
    ) {
      return true;
    }
    
    return false;
  }
  
  /**
   * Schedule periodic security tasks
   */
  private scheduleSecurityTasks(): void {
    // Expire outdated approval requests every hour
    setInterval(async () => {
      try {
        const expiredCount = await multiSignatureGateway.expireOutdatedRequests();
        if (expiredCount > 0) {
          this.logger.debug(`Expired ${expiredCount} outdated approval requests`);
        }
      } catch (error) {
        this.logger.error('Error expiring outdated approval requests', error);
      }
    }, 60 * 60 * 1000); // 1 hour
    
    // Run integrity verification daily
    setInterval(async () => {
      try {
        await dataPersistenceService.verifySystemIntegrity();
        this.logger.debug('Daily system integrity verification completed');
      } catch (error) {
        this.logger.error('Error during system integrity verification', error);
      }
    }, 24 * 60 * 60 * 1000); // 24 hours
  }
  
  /**
   * Map HTTP request to a transaction type for behavioral analysis
   */
  private mapRequestToTransactionType(req: Request): string {
    const method = req.method.toUpperCase();
    const path = req.path.toLowerCase();
    
    if (path.includes('vault')) {
      if (method === 'POST') return 'CREATE_VAULT';
      if (method === 'PUT') return 'MODIFY_VAULT';
      if (method === 'DELETE') return 'DELETE_VAULT';
      if (path.includes('unlock')) return 'UNLOCK_VAULT';
    }
    
    if (path.includes('asset') || path.includes('token')) {
      if (method === 'POST') return 'DEPOSIT_ASSET';
      if (method === 'PUT') return 'TRANSFER_ASSET';
      if (method === 'DELETE') return 'WITHDRAW_ASSET';
    }
    
    if (path.includes('beneficiar')) {
      if (method === 'POST') return 'ADD_BENEFICIARY';
      if (method === 'PUT') return 'MODIFY_BENEFICIARY';
      if (method === 'DELETE') return 'REMOVE_BENEFICIARY';
    }
    
    if (path.includes('signature')) {
      return 'SIGNATURE_OPERATION';
    }
    
    return 'UNKNOWN_OPERATION';
  }
  
  /**
   * Extract device type from request
   */
  private extractDeviceType(req: Request): string {
    const userAgent = req.headers['user-agent'] || '';
    
    if (/mobile|android|iphone|ipad|ipod|blackberry|iemobile|opera mini/i.test(userAgent)) {
      return 'mobile';
    } else if (/tablet|ipad/i.test(userAgent)) {
      return 'tablet';
    } else if (/googlebot|bingbot|yandexbot|duckduckbot|slurp|baiduspider/i.test(userAgent)) {
      return 'bot';
    } else {
      return 'desktop';
    }
  }
}

// Export a singleton instance for use throughout the application
export const securityServiceManager = new SecurityServiceManager();
