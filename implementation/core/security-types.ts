/**
 * Security Type Definitions
 */

export enum SecurityEventType {
  // System Events
  SYSTEM_STARTUP = 'SYSTEM_STARTUP',
  SYSTEM_SHUTDOWN = 'SYSTEM_SHUTDOWN',
  CONFIGURATION_CHANGE = 'CONFIGURATION_CHANGE',

  // Authentication Events
  LOGIN_SUCCESS = 'LOGIN_SUCCESS',
  LOGIN_FAILURE = 'LOGIN_FAILURE',
  LOGOUT = 'LOGOUT',
  PASSWORD_CHANGE = 'PASSWORD_CHANGE',

  // Vault Access Events
  VAULT_ACCESS_ATTEMPT = 'VAULT_ACCESS_ATTEMPT',
  VAULT_ACCESS_SUCCESS = 'VAULT_ACCESS_SUCCESS',
  VAULT_ACCESS_FAILURE = 'VAULT_ACCESS_FAILURE',
  VAULT_CREATION = 'VAULT_CREATION',
  VAULT_MODIFICATION = 'VAULT_MODIFICATION',
  VAULT_DELETION = 'VAULT_DELETION',

  // Cross-Chain Events
  CROSS_CHAIN_VERIFICATION = 'CROSS_CHAIN_VERIFICATION',
  CROSS_CHAIN_MISMATCH = 'CROSS_CHAIN_MISMATCH',
  CROSS_CHAIN_SYNC = 'CROSS_CHAIN_SYNC',
  CROSS_CHAIN_ERROR = 'CROSS_CHAIN_ERROR',

  // Security Alert Events
  SUSPICIOUS_ACTIVITY = 'SUSPICIOUS_ACTIVITY',
  RATE_LIMIT_EXCEEDED = 'RATE_LIMIT_EXCEEDED',
  UNUSUAL_PATTERN = 'UNUSUAL_PATTERN',
  AUTHORIZATION_FAILURE = 'AUTHORIZATION_FAILURE',

  // Failover Events
  FAILOVER_INITIATED = 'FAILOVER_INITIATED',
  FAILOVER_SUCCESS = 'FAILOVER_SUCCESS',
  FAILOVER_FAILURE = 'FAILOVER_FAILURE',
  FALLBACK_CHAIN_SELECTED = 'FALLBACK_CHAIN_SELECTED',

  // Network Events
  NETWORK_ERROR = 'NETWORK_ERROR',
  NETWORK_LATENCY = 'NETWORK_LATENCY',
  NODE_UNREACHABLE = 'NODE_UNREACHABLE',
  SYNC_DELAY = 'SYNC_DELAY',

  // Zero-Knowledge Events
  ZK_PROOF_SUCCESS = 'ZK_PROOF_SUCCESS',
  ZK_PROOF_FAILURE = 'ZK_PROOF_FAILURE',
  ZK_SERVICE_INIT = 'ZK_SERVICE_INIT',
  ZK_SERVICE_ERROR = 'ZK_SERVICE_ERROR',

  // Quantum-Resistant Encryption Events
  QRE_KEY_GENERATION = 'QRE_KEY_GENERATION',
  QRE_ENCRYPTION = 'QRE_ENCRYPTION',
  QRE_DECRYPTION = 'QRE_DECRYPTION',
  QRE_ERROR = 'QRE_ERROR',

  // Maintenance Events
  MAINTENANCE_START = 'MAINTENANCE_START',
  MAINTENANCE_END = 'MAINTENANCE_END',
  SCHEDULED_BACKUP = 'SCHEDULED_BACKUP',
  SYSTEM_UPDATE = 'SYSTEM_UPDATE'
}

export enum SecurityAlertSeverity {
  LOW = 'LOW',
  MEDIUM = 'MEDIUM',
  HIGH = 'HIGH',
  CRITICAL = 'CRITICAL'
}

export enum SecurityEventStatus {
  PENDING = 'PENDING',
  PROCESSED = 'PROCESSED',
  RESOLVED = 'RESOLVED',
  IGNORED = 'IGNORED'
}

export interface SecurityEvent {
  id: string;
  type: SecurityEventType;
  timestamp: number;
  source: string;
  severity: SecurityAlertSeverity;
  details: any;
  status: SecurityEventStatus;
  relatedEvents?: string[]; // IDs of related events
}

export interface SecurityAlert {
  id: string;
  severity: SecurityAlertSeverity;
  message: string;
  timestamp: number;
  resolved: boolean;
  relatedEvents?: string[]; // IDs of related events
  metadata?: Record<string, any>;
}

export interface FailoverEvent {
  vaultId: string;
  primaryChain: string;
  fallbackChain?: string;
  strategy: number;
  reason: string;
  timestamp: number;
  success?: boolean;
  errorMessage?: string;
}