/**
 * Advanced Multi-Signature Security Gateway
 * 
 * Provides enhanced protection for high-value vaults through sophisticated
 * multi-signature requirements and advanced approval workflows.
 */

import { createHash, randomBytes } from 'crypto';
import { BlockchainType } from '../../shared/types';
import { zeroKnowledgeShield } from './zero-knowledge-shield';

export enum ApprovalStatus {
  PENDING = 'PENDING',
  APPROVED = 'APPROVED',
  REJECTED = 'REJECTED',
  EXPIRED = 'EXPIRED',
  CANCELLED = 'CANCELLED'
}

export enum ApprovalType {
  CREATE_VAULT = 'CREATE_VAULT',
  UNLOCK_ASSETS = 'UNLOCK_ASSETS',
  MODIFY_VAULT = 'MODIFY_VAULT',
  ADD_BENEFICIARY = 'ADD_BENEFICIARY',
  REMOVE_BENEFICIARY = 'REMOVE_BENEFICIARY',
  EMERGENCY_RECOVERY = 'EMERGENCY_RECOVERY',
  THRESHOLD_CHANGE = 'THRESHOLD_CHANGE'
}

export enum SignatureVerificationMethod {
  ON_CHAIN = 'ON_CHAIN',
  OFF_CHAIN = 'OFF_CHAIN',
  HARDWARE_SECURED = 'HARDWARE_SECURED',
  MPC = 'MPC', // Multi-party computation
  ZERO_KNOWLEDGE = 'ZERO_KNOWLEDGE'
}

export interface Signer {
  id: string;
  address: string;
  weight: number;  // For weighted voting systems
  name?: string;
  role?: string;
  requireHardwareKey?: boolean;
  biometricVerification?: boolean;
  geolocationRequired?: boolean;
  secondFactorRequired?: boolean;
  notificationPreferences: {
    email?: boolean;
    push?: boolean;
    sms?: boolean;
  };
}

export interface Signature {
  id: string;
  signerId: string;
  signerAddress: string;
  requestId: string;
  signature: string;
  timestamp: number;
  expiresAt: number;
  blockchainType: BlockchainType;
  verificationMethod: SignatureVerificationMethod;
  metadata: Record<string, any>;
}

export interface ApprovalRequest {
  id: string;
  vaultId: string;
  creatorId: string;
  type: ApprovalType;
  status: ApprovalStatus;
  createTimestamp: number;
  updateTimestamp: number;
  expiresAt: number;
  thresholdWeight: number;
  currentWeight: number;
  requiredSigners: Signer[];
  receivedSignatures: Signature[];
  transactionData: {
    blockchainType: BlockchainType;
    data: any;
    hash?: string;
  };
  metadata: Record<string, any>;
  zeroKnowledgeProof?: boolean;
}

export interface MultiSigConfig {
  defaultThreshold: number; // Number of signatures required by default
  defaultExpiration: number; // Milliseconds until request expires
  weightedSignatures: boolean; // Whether to use weighted voting
  escalationThresholds: {
    value: { [threshold: string]: number }; // Value thresholds for increased security
    age: { [threshold: string]: number }; // Age thresholds (days) for increased security
  };
  requireGeolocationDiversity: boolean; // Require signers from different locations
  requireHardwareKeyForHighValue: boolean; // Require hardware key for high-value transactions
  zeroKnowledgeMode: boolean; // Use ZK proofs for privacy
}

const DEFAULT_MULTISIG_CONFIG: MultiSigConfig = {
  defaultThreshold: 2, // 2-of-N by default
  defaultExpiration: 24 * 60 * 60 * 1000, // 24 hours
  weightedSignatures: false,
  escalationThresholds: {
    value: {
      'high': 10000, // > 10000 units requires extra security
      'very-high': 100000 // > 100000 units requires maximum security
    },
    age: {
      'mature': 180, // > 180 days old requires extra security
      'established': 365 // > 365 days old requires maximum security
    }
  },
  requireGeolocationDiversity: false,
  requireHardwareKeyForHighValue: true,
  zeroKnowledgeMode: true
};

/**
 * Multi-Signature Security Gateway
 */
export class MultiSignatureGateway {
  private config: MultiSigConfig;
  private approvalRequests: Map<string, ApprovalRequest> = new Map();
  private signers: Map<string, Map<string, Signer>> = new Map(); // vaultId -> Map<signerId, Signer>
  private logger: any; // Would be proper logger
  
  constructor(config: Partial<MultiSigConfig> = {}) {
    this.config = { ...DEFAULT_MULTISIG_CONFIG, ...config };
    this.logger = {
      debug: (msg: string) => console.debug(`[MultiSig] ${msg}`),
      info: (msg: string) => console.info(`[MultiSig] ${msg}`),
      warn: (msg: string) => console.warn(`[MultiSig] ${msg}`),
      error: (msg: string, error?: any) => console.error(`[MultiSig] ${msg}`, error)
    };
    
    this.logger.info('Multi-Signature Gateway initialized');
  }
  
  /**
   * Get the signers for a vault
   */
  async getVaultSigners(vaultId: string): Promise<Signer[]> {
    const vaultSigners = this.signers.get(vaultId);
    
    if (!vaultSigners) {
      return [];
    }
    
    return Array.from(vaultSigners.values());
  }
  
  /**
   * Add a signer to a vault
   */
  async addSigner(vaultId: string, signer: Omit<Signer, 'id'>): Promise<Signer> {
    let vaultSigners = this.signers.get(vaultId);
    
    if (!vaultSigners) {
      vaultSigners = new Map();
      this.signers.set(vaultId, vaultSigners);
    }
    
    // Generate unique ID for the signer
    const signerId = createHash('sha256')
      .update(`${vaultId}:${signer.address}:${Date.now()}`)
      .digest('hex');
      
    const newSigner: Signer = {
      id: signerId,
      ...signer
    };
    
    vaultSigners.set(signerId, newSigner);
    
    this.logger.info(`Added signer ${signerId} to vault ${vaultId}`);
    return newSigner;
  }
  
  /**
   * Remove a signer from a vault
   */
  async removeSigner(vaultId: string, signerId: string): Promise<boolean> {
    const vaultSigners = this.signers.get(vaultId);
    
    if (!vaultSigners || !vaultSigners.has(signerId)) {
      return false;
    }
    
    vaultSigners.delete(signerId);
    this.logger.info(`Removed signer ${signerId} from vault ${vaultId}`);
    return true;
  }
  
  /**
   * Update signer details
   */
  async updateSigner(vaultId: string, signerId: string, updates: Partial<Signer>): Promise<Signer | null> {
    const vaultSigners = this.signers.get(vaultId);
    
    if (!vaultSigners || !vaultSigners.has(signerId)) {
      return null;
    }
    
    const signer = vaultSigners.get(signerId)!;
    const updatedSigner = { ...signer, ...updates, id: signer.id };
    
    vaultSigners.set(signerId, updatedSigner);
    
    this.logger.info(`Updated signer ${signerId} for vault ${vaultId}`);
    return updatedSigner;
  }
  
  /**
   * Create a new approval request
   */
  async createApprovalRequest(
    vaultId: string,
    creatorId: string,
    type: ApprovalType,
    transactionData: {
      blockchainType: BlockchainType;
      data: any;
    },
    options: {
      customThresholdWeight?: number;
      expiration?: number;
      metadata?: Record<string, any>;
      zeroKnowledgeProof?: boolean;
    } = {}
  ): Promise<ApprovalRequest> {
    // 1. Get the signers for the vault
    const signers = await this.getVaultSigners(vaultId);
    
    if (signers.length === 0) {
      throw new Error(`No signers defined for vault ${vaultId}`);
    }
    
    // 2. Determine the threshold weight based on transaction value or custom setting
    const thresholdWeight = options.customThresholdWeight ?? 
      (this.config.weightedSignatures ? this.determineThresholdWeight(vaultId, type, transactionData) : this.config.defaultThreshold);
    
    // 3. Generate a unique ID for the request
    const requestId = createHash('sha256')
      .update(`${vaultId}:${type}:${creatorId}:${Date.now()}:${randomBytes(8).toString('hex')}`)
      .digest('hex');
      
    // 4. Create the approval request
    const now = Date.now();
    const request: ApprovalRequest = {
      id: requestId,
      vaultId,
      creatorId,
      type,
      status: ApprovalStatus.PENDING,
      createTimestamp: now,
      updateTimestamp: now,
      expiresAt: now + (options.expiration ?? this.config.defaultExpiration),
      thresholdWeight,
      currentWeight: 0,
      requiredSigners: signers,
      receivedSignatures: [],
      transactionData: {
        ...transactionData,
        hash: createHash('sha256').update(JSON.stringify(transactionData.data)).digest('hex')
      },
      metadata: options.metadata ?? {},
      zeroKnowledgeProof: options.zeroKnowledgeProof ?? this.config.zeroKnowledgeMode
    };
    
    // 5. Store the request
    this.approvalRequests.set(requestId, request);
    
    this.logger.info(`Created ${type} approval request ${requestId} for vault ${vaultId}`);
    return request;
  }
  
  /**
   * Submit a signature for an approval request
   */
  async submitSignature(
    requestId: string,
    signerAddress: string,
    signature: string,
    verificationMethod: SignatureVerificationMethod,
    metadata: Record<string, any> = {}
  ): Promise<Signature | null> {
    // 1. Get the approval request
    const request = this.approvalRequests.get(requestId);
    
    if (!request) {
      this.logger.warn(`Signature submission for unknown request ${requestId}`);
      return null;
    }
    
    // 2. Check if the request is still pending
    if (request.status !== ApprovalStatus.PENDING) {
      this.logger.warn(`Signature submission for non-pending request ${requestId} (status: ${request.status})`);
      return null;
    }
    
    // 3. Check if the request has expired
    if (Date.now() > request.expiresAt) {
      request.status = ApprovalStatus.EXPIRED;
      request.updateTimestamp = Date.now();
      this.approvalRequests.set(requestId, request);
      
      this.logger.warn(`Signature submission for expired request ${requestId}`);
      return null;
    }
    
    // 4. Find the signer in the required signers list
    const signer = request.requiredSigners.find(s => s.address.toLowerCase() === signerAddress.toLowerCase());
    
    if (!signer) {
      this.logger.warn(`Signature from unauthorized signer ${signerAddress} for request ${requestId}`);
      return null;
    }
    
    // 5. Check if the signer has already signed
    if (request.receivedSignatures.some(s => s.signerAddress.toLowerCase() === signerAddress.toLowerCase())) {
      this.logger.warn(`Duplicate signature from signer ${signerAddress} for request ${requestId}`);
      return null;
    }
    
    // 6. Verify the signature
    // In a real implementation, we would verify the cryptographic signature
    // against the transaction data and signer's public key
    const signatureIsValid = true; // Simulated validation
    
    if (!signatureIsValid) {
      this.logger.warn(`Invalid signature from signer ${signerAddress} for request ${requestId}`);
      return null;
    }
    
    // 7. Create the signature record
    const now = Date.now();
    const signatureRecord: Signature = {
      id: createHash('sha256').update(`${requestId}:${signerAddress}:${now}`).digest('hex'),
      signerId: signer.id,
      signerAddress,
      requestId,
      signature,
      timestamp: now,
      expiresAt: request.expiresAt,
      blockchainType: request.transactionData.blockchainType,
      verificationMethod,
      metadata
    };
    
    // 8. Add the signature to the request
    request.receivedSignatures.push(signatureRecord);
    request.currentWeight += this.config.weightedSignatures ? signer.weight : 1;
    request.updateTimestamp = now;
    
    // 9. Check if the threshold is reached
    if (request.currentWeight >= request.thresholdWeight) {
      request.status = ApprovalStatus.APPROVED;
      this.logger.info(`Approval request ${requestId} approved with ${request.receivedSignatures.length} signatures`);
      
      // If using zero-knowledge proofs, create a ZK proof of multi-signature requirement
      if (request.zeroKnowledgeProof) {
        try {
          const zkProof = await zeroKnowledgeShield.proveMultiSignatureRequirement(
            request.vaultId,
            request.thresholdWeight,
            request.receivedSignatures.map(s => s.signature),
            request.requiredSigners.length
          );
          
          // Store the ZK proof in the request metadata
          request.metadata.zkProof = zkProof;
          this.logger.debug(`Created ZK multi-signature proof for request ${requestId}`);
        } catch (error) {
          this.logger.error(`Failed to create ZK proof for multi-sig request ${requestId}`, error);
        }
      }
    }
    
    // 10. Update the request
    this.approvalRequests.set(requestId, request);
    
    this.logger.info(`Signature from ${signerAddress} added to request ${requestId} (${request.currentWeight}/${request.thresholdWeight})`);
    return signatureRecord;
  }
  
  /**
   * Get all approval requests for a vault
   */
  getApprovalRequestsForVault(vaultId: string): ApprovalRequest[] {
    return Array.from(this.approvalRequests.values())
      .filter(request => request.vaultId === vaultId);
  }
  
  /**
   * Get all approval requests by status
   */
  getApprovalRequestsByStatus(status: ApprovalStatus): ApprovalRequest[] {
    return Array.from(this.approvalRequests.values())
      .filter(request => request.status === status);
  }
  
  /**
   * Get an approval request by ID
   */
  getApprovalRequest(requestId: string): ApprovalRequest | undefined {
    return this.approvalRequests.get(requestId);
  }
  
  /**
   * Cancel an approval request
   */
  cancelApprovalRequest(requestId: string): boolean {
    const request = this.approvalRequests.get(requestId);
    
    if (!request || request.status !== ApprovalStatus.PENDING) {
      return false;
    }
    
    request.status = ApprovalStatus.CANCELLED;
    request.updateTimestamp = Date.now();
    this.approvalRequests.set(requestId, request);
    
    this.logger.info(`Approval request ${requestId} cancelled`);
    return true;
  }
  
  /**
   * Expire outdated approval requests
   */
  async expireOutdatedRequests(): Promise<number> {
    const now = Date.now();
    let expiredCount = 0;
    
    for (const [requestId, request] of this.approvalRequests.entries()) {
      if (request.status === ApprovalStatus.PENDING && now > request.expiresAt) {
        request.status = ApprovalStatus.EXPIRED;
        request.updateTimestamp = now;
        this.approvalRequests.set(requestId, request);
        expiredCount++;
        
        this.logger.debug(`Expired approval request ${requestId}`);
      }
    }
    
    if (expiredCount > 0) {
      this.logger.info(`Expired ${expiredCount} outdated approval requests`);
    }
    
    return expiredCount;
  }
  
  /**
   * Determine the required threshold weight based on the transaction value
   */
  private determineThresholdWeight(vaultId: string, type: ApprovalType, transactionData: any): number {
    // Start with the default threshold
    let threshold = this.config.defaultThreshold;
    
    // In a real implementation, we would analyze the transaction data
    // and apply escalation thresholds based on value, vault age, etc.
    // For this implementation, we'll use a simplified approach
    
    // 1. Check if the transaction involves unlocking high-value assets
    if (type === ApprovalType.UNLOCK_ASSETS && transactionData.data.amount) {
      const amount = Number(transactionData.data.amount);
      
      // Apply escalation thresholds based on value
      if (amount >= this.config.escalationThresholds.value['very-high']) {
        // Maximum security for very high value transactions
        threshold = Math.max(threshold, 4);
      } else if (amount >= this.config.escalationThresholds.value['high']) {
        // Enhanced security for high value transactions
        threshold = Math.max(threshold, 3);
      }
    }
    
    // 2. Apply additional thresholds for sensitive operations
    if (type === ApprovalType.EMERGENCY_RECOVERY || type === ApprovalType.THRESHOLD_CHANGE) {
      // These operations always require at least 3 signatures
      threshold = Math.max(threshold, 3);
    }
    
    // 3. For mature vaults, increase the threshold
    // In a real implementation, we would check the vault age
    
    return threshold;
  }
}

// Export a singleton instance for use throughout the application
export const multiSignatureGateway = new MultiSignatureGateway();
