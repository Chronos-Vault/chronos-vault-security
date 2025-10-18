/**
 * Security Audit Service
 * 
 * This service integrates the security audit framework with the rest of the application.
 * It provides a simplified interface for creating and managing security audits.
 */

import { getSecurityAuditFramework } from './audit-framework';
import { securityLogger, SecurityEventType } from '../monitoring/security-logger';
import { EthereumConnector } from '../blockchain/ethereum-connector';
import { SolanaConnector } from '../blockchain/solana-connector';
import { TonConnector } from '../blockchain/ton-connector';
import { BitcoinConnector } from '../blockchain/bitcoin-connector';
import config from '../config';
import { 
  SecurityAuditLevel, 
  AuditableOperation 
} from '../../shared/types/security-types';

/**
 * Security Audit Service
 */
export class SecurityAuditService {
  private static instance: SecurityAuditService;
  private initialized: boolean = false;
  
  /**
   * Private constructor for singleton pattern
   */
  private constructor() {}
  
  /**
   * Get singleton instance
   */
  public static getInstance(): SecurityAuditService {
    if (!SecurityAuditService.instance) {
      SecurityAuditService.instance = new SecurityAuditService();
    }
    return SecurityAuditService.instance;
  }
  
  /**
   * Initialize the security audit service
   */
  public initialize(): void {
    if (this.initialized) {
      securityLogger.warn('Security Audit Service already initialized', SecurityEventType.SYSTEM_ERROR);
      return;
    }
    
    try {
      // Create blockchain connectors - pass isTestnet parameter
      const ethConnector = new EthereumConnector(config.blockchainConfig.ethereum.isTestnet);
      const solConnector = new SolanaConnector(config.blockchainConfig.solana.isTestnet);
      const tonConnector = new TonConnector(config.blockchainConfig.ton.isTestnet);
      const btcConnector = new BitcoinConnector(config.blockchainConfig.bitcoin.isTestnet);
      
      // Create a map of connectors
      const connectors = new Map();
      connectors.set('ethereum', ethConnector);
      connectors.set('solana', solConnector);
      connectors.set('ton', tonConnector);
      connectors.set('bitcoin', btcConnector);
      
      // Initialize the audit framework with the connectors
      const auditFramework = getSecurityAuditFramework();
      auditFramework.initialize(connectors);
      
      this.initialized = true;
      securityLogger.info('Security Audit Service initialized successfully', SecurityEventType.SYSTEM_ERROR);
    } catch (error) {
      securityLogger.error('Failed to initialize Security Audit Service', SecurityEventType.SYSTEM_ERROR, { error });
      throw new Error(`Failed to initialize Security Audit Service: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  
  /**
   * Shut down the security audit service
   */
  public shutdown(): void {
    if (!this.initialized) {
      return;
    }
    
    try {
      // Shut down the audit framework
      const auditFramework = getSecurityAuditFramework();
      auditFramework.shutdown();
      
      this.initialized = false;
      securityLogger.info('Security Audit Service shut down successfully', SecurityEventType.SYSTEM_ERROR);
    } catch (error) {
      securityLogger.error('Error shutting down Security Audit Service', SecurityEventType.SYSTEM_ERROR, { error });
    }
  }
  
  /**
   * Create a new vault creation audit
   */
  public auditVaultCreation(
    vaultId: string,
    chainId: string,
    securityLevel: number,
    ownerAddress: string,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'vault_creation',
      'high',
      {
        vaultId,
        chainId,
        securityLevel,
        ownerAddress,
        timeLock: metadata.timeLock,
        secondaryChains: metadata.secondaryChains,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new vault unlock audit
   */
  public auditVaultUnlock(
    vaultId: string,
    chainId: string,
    requesterAddress: string,
    isOwner: boolean,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'vault_unlock',
      'high',
      {
        vaultId,
        chainId,
        requesterAddress,
        isOwner,
        isBeneficiary: metadata.isBeneficiary || false,
        unlockTime: metadata.unlockTime,
        securityLevel: metadata.securityLevel,
        crossChainVerificationComplete: metadata.crossChainVerificationComplete,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new cross-chain verification audit
   */
  public auditCrossChainVerification(
    vaultId: string,
    primaryChain: string,
    secondaryChains: string[],
    verificationResults: Array<{ chainId: string; success: boolean; timestamp: string; }>,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'cross_chain_verification',
      'high',
      {
        vaultId,
        primaryChain,
        secondaryChains,
        verificationResults,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new beneficiary addition audit
   */
  public auditBeneficiaryAddition(
    vaultId: string,
    chainId: string,
    ownerAddress: string,
    beneficiaryAddress: string,
    isOwner: boolean,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'beneficiary_addition',
      'medium',
      {
        vaultId,
        chainId,
        ownerAddress,
        beneficiaryAddress,
        isOwner,
        requesterAddress: metadata.requesterAddress || ownerAddress,
        existingBeneficiaries: metadata.existingBeneficiaries,
        securityLevel: metadata.securityLevel,
        secondaryChainUpdates: metadata.secondaryChainUpdates,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new asset deposit audit
   */
  public auditAssetDeposit(
    vaultId: string,
    chainId: string,
    depositorAddress: string,
    amount: string | number,
    assetType: string,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'asset_deposit',
      'medium',
      {
        vaultId,
        chainId,
        depositorAddress,
        amount,
        assetType,
        historicalAverage: metadata.historicalAverage,
        restrictedDepositors: metadata.restrictedDepositors,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new security level change audit
   */
  public auditSecurityLevelChange(
    vaultId: string,
    chainId: string,
    ownerAddress: string,
    oldLevel: number,
    newLevel: number,
    isOwner: boolean,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'security_level_change',
      'high',
      {
        vaultId,
        chainId,
        ownerAddress,
        oldLevel,
        newLevel,
        isOwner,
        requesterAddress: metadata.requesterAddress || ownerAddress,
        secondaryChains: metadata.secondaryChains,
        vaultValue: metadata.vaultValue,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new wallet connection audit
   */
  public auditWalletConnection(
    chainId: string,
    walletAddress: string,
    walletType: string,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'wallet_connection',
      'medium',
      {
        chainId,
        walletAddress,
        walletType,
        recentConnections: metadata.recentConnections,
        userGeolocation: metadata.userGeolocation,
        previousGeolocation: metadata.previousGeolocation,
        timeSinceLastLogin: metadata.timeSinceLastLogin,
        ...metadata
      }
    );
  }
  
  /**
   * Create a new transaction submission audit
   */
  public auditTransactionSubmission(
    chainId: string,
    walletAddress: string,
    transactionType: string,
    transactionData: Record<string, any>,
    metadata: Record<string, any> = {}
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    
    return auditFramework.createAudit(
      'transaction_submission',
      'high',
      {
        chainId,
        walletAddress,
        transactionType,
        transactionData,
        averageTransactionValue: metadata.averageTransactionValue,
        suspiciousContracts: metadata.suspiciousContracts,
        ...metadata
      }
    );
  }
  
  /**
   * Create a generic audit
   */
  public createAudit(
    operation: AuditableOperation,
    level: SecurityAuditLevel,
    metadata: Record<string, any>
  ): string {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    return auditFramework.createAudit(operation, level, metadata);
  }
  
  /**
   * Get audit by ID
   */
  public getAuditById(auditId: string) {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    return auditFramework.getAuditById(auditId);
  }
  
  /**
   * Get all completed audits
   */
  public getCompletedAudits() {
    this.ensureInitialized();
    
    const auditFramework = getSecurityAuditFramework();
    return auditFramework.getCompletedAudits();
  }
  
  /**
   * Ensure the service is initialized
   */
  private ensureInitialized(): void {
    if (!this.initialized) {
      throw new Error('Security Audit Service not initialized');
    }
  }
}

// Export singleton instance getter
export const getSecurityAuditService = SecurityAuditService.getInstance;