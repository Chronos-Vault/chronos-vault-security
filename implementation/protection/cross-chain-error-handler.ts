/**
 * Cross-Chain Error Handler
 * 
 * A specialized error handling system for cross-chain operations. This handler
 * categorizes errors and provides appropriate recovery strategies specific to
 * blockchain types and error patterns.
 */

import { securityLogger, SecurityEventType } from '../monitoring/security-logger';
import { BlockchainType } from '../../shared/types';
import config from '../config';

// Error categories help us identify and handle errors appropriately
export enum CrossChainErrorCategory {
  CONNECTION_FAILURE = 'connection_failure',
  TRANSACTION_FAILURE = 'transaction_failure',
  VALIDATION_FAILURE = 'validation_failure', 
  RATE_LIMIT_EXCEEDED = 'rate_limit_exceeded',
  VERIFICATION_FAILURE = 'verification_failure',
  ASSET_MISMATCH = 'asset_mismatch',
  UNAUTHORIZED_ACCESS = 'unauthorized_access',
  INVALID_PARAMETERS = 'invalid_parameters',
  NODE_SYNCING = 'node_syncing',
  CONSENSUS_FAILURE = 'consensus_failure',
  CROSS_CHAIN_SYNC_ERROR = 'cross_chain_sync_error',
  CHAIN_UNAVAILABLE = 'chain_unavailable',
  VERIFICATION_TIMEOUT = 'verification_timeout',
  UNKNOWN = 'unknown'
}

// Context for error handling
export interface ErrorContext {
  category?: CrossChainErrorCategory;
  blockchain?: BlockchainType;
  operation?: string;
  retryCount?: number;
  vaultId?: string;
  transactionId?: string;
  metadata?: Record<string, any>;
}

// Represents a processed cross-chain error
export interface CrossChainError {
  originalError: any;
  message: string;
  category: CrossChainErrorCategory;
  blockchain?: BlockchainType;
  recoverable: boolean;
  retryStrategy?: RetryStrategy;
  solution?: string;
  metadata?: Record<string, any>;
}

// Retry strategy for recoverable errors
export interface RetryStrategy {
  shouldRetry: boolean;
  delayMs: number;
  maxRetries: number;
  exponentialBackoff: boolean;
  alternativeEndpoint?: string;
  fallbackChain?: BlockchainType;
}

/**
 * Error patterns for different blockchains to match against
 */
const errorPatterns = {
  ethereum: [
    { 
      pattern: /(insufficient funds|gas price|gas too low)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: true,
      solution: 'Adjust gas price or reduce transaction complexity'
    },
    { 
      pattern: /(nonce too low|nonce too high|invalid nonce)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: true,
      solution: 'Synchronize nonce with blockchain state'
    },
    { 
      pattern: /(pending|queue full|already known)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: true,
      solution: 'Wait for network congestion to clear'
    },
    { 
      pattern: /(connection refused|timeout|econnreset|econnaborted)/i,
      category: CrossChainErrorCategory.CONNECTION_FAILURE,
      recoverable: true,
      solution: 'Switch to alternate Ethereum RPC endpoint'
    },
    { 
      pattern: /(rate limit|too many requests|429)/i,
      category: CrossChainErrorCategory.RATE_LIMIT_EXCEEDED,
      recoverable: true,
      solution: 'Implement exponential backoff and reduce request frequency'
    },
    { 
      pattern: /(syncing|not up to date|still syncing)/i,
      category: CrossChainErrorCategory.NODE_SYNCING,
      recoverable: true,
      solution: 'Switch to a fully synced node or wait for sync completion'
    }
  ],
  solana: [
    { 
      pattern: /(blockhash not found|block height exceeded|too old|expired)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: true,
      solution: 'Refresh blockhash and resend transaction'
    },
    { 
      pattern: /(insufficient funds|insufficient lamports)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: false,
      solution: 'Ensure wallet has sufficient SOL for the transaction'
    },
    { 
      pattern: /(socket hang up|timeout|econnreset|econnrefused)/i,
      category: CrossChainErrorCategory.CONNECTION_FAILURE,
      recoverable: true,
      solution: 'Switch to alternate Solana RPC endpoint'
    },
    { 
      pattern: /(too many requests|429|rate limit)/i,
      category: CrossChainErrorCategory.RATE_LIMIT_EXCEEDED,
      recoverable: true,
      solution: 'Implement exponential backoff and reduce request frequency'
    },
    { 
      pattern: /(invalid.*signature|signature verification failed)/i,
      category: CrossChainErrorCategory.VALIDATION_FAILURE,
      recoverable: false,
      solution: 'Check signature generation process'
    }
  ],
  ton: [
    { 
      pattern: /(insufficient funds|not enough balance)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: false,
      solution: 'Ensure wallet has sufficient TON for the transaction'
    },
    { 
      pattern: /(connection refused|timeout|network error)/i,
      category: CrossChainErrorCategory.CONNECTION_FAILURE,
      recoverable: true,
      solution: 'Switch to alternate TON endpoint'
    },
    { 
      pattern: /(rate limit|too many requests|429)/i,
      category: CrossChainErrorCategory.RATE_LIMIT_EXCEEDED,
      recoverable: true,
      solution: 'Implement exponential backoff and reduce request frequency'
    },
    { 
      pattern: /(invalid address|incorrect address)/i,
      category: CrossChainErrorCategory.VALIDATION_FAILURE,
      recoverable: false,
      solution: 'Verify TON address format'
    },
    { 
      pattern: /(cell underflow|cell overflow|not enough bytes)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: false,
      solution: 'Check TON cell serialization/deserialization logic'
    }
  ],
  bitcoin: [
    { 
      pattern: /(insufficient funds|insufficient priority)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: true,
      solution: 'Increase fee rate or ensure sufficient BTC balance'
    },
    { 
      pattern: /(connection refused|timeout|network error)/i,
      category: CrossChainErrorCategory.CONNECTION_FAILURE,
      recoverable: true, 
      solution: 'Switch to alternate Bitcoin node'
    },
    { 
      pattern: /(rate limit|too many requests|429)/i,
      category: CrossChainErrorCategory.RATE_LIMIT_EXCEEDED,
      recoverable: true,
      solution: 'Implement exponential backoff and reduce request frequency'
    },
    { 
      pattern: /(dust threshold|output too small)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: false,
      solution: 'Ensure outputs are above the dust threshold'
    },
    { 
      pattern: /(transaction already in block chain|already confirmed)/i,
      category: CrossChainErrorCategory.TRANSACTION_FAILURE,
      recoverable: false,
      solution: 'Transaction already confirmed, no action needed'
    }
  ]
};

/**
 * Default retry strategies for different error categories
 */
const defaultRetryStrategies: Record<CrossChainErrorCategory, RetryStrategy> = {
  [CrossChainErrorCategory.CONNECTION_FAILURE]: {
    shouldRetry: true,
    delayMs: 2000,
    maxRetries: 5,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.TRANSACTION_FAILURE]: {
    shouldRetry: true,
    delayMs: 5000,
    maxRetries: 3,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.VALIDATION_FAILURE]: {
    shouldRetry: false,
    delayMs: 0,
    maxRetries: 0,
    exponentialBackoff: false
  },
  [CrossChainErrorCategory.RATE_LIMIT_EXCEEDED]: {
    shouldRetry: true,
    delayMs: 10000,
    maxRetries: 3,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.VERIFICATION_FAILURE]: {
    shouldRetry: true,
    delayMs: 3000,
    maxRetries: 2,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.ASSET_MISMATCH]: {
    shouldRetry: false,
    delayMs: 0,
    maxRetries: 0,
    exponentialBackoff: false
  },
  [CrossChainErrorCategory.UNAUTHORIZED_ACCESS]: {
    shouldRetry: false,
    delayMs: 0,
    maxRetries: 0,
    exponentialBackoff: false
  },
  [CrossChainErrorCategory.INVALID_PARAMETERS]: {
    shouldRetry: false,
    delayMs: 0,
    maxRetries: 0,
    exponentialBackoff: false
  },
  [CrossChainErrorCategory.NODE_SYNCING]: {
    shouldRetry: true,
    delayMs: 30000,
    maxRetries: 2,
    exponentialBackoff: false
  },
  [CrossChainErrorCategory.CONSENSUS_FAILURE]: {
    shouldRetry: true,
    delayMs: 5000,
    maxRetries: 3,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.CROSS_CHAIN_SYNC_ERROR]: {
    shouldRetry: true,
    delayMs: 7000,
    maxRetries: 4,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.CHAIN_UNAVAILABLE]: {
    shouldRetry: true,
    delayMs: 15000,
    maxRetries: 3,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.VERIFICATION_TIMEOUT]: {
    shouldRetry: true,
    delayMs: 8000,
    maxRetries: 2,
    exponentialBackoff: true
  },
  [CrossChainErrorCategory.UNKNOWN]: {
    shouldRetry: true,
    delayMs: 5000,
    maxRetries: 1,
    exponentialBackoff: false
  }
};

/**
 * Fallback chains for different blockchains
 */
const fallbackChains: Record<BlockchainType, BlockchainType> = {
  ethereum: 'solana',
  solana: 'ton',
  ton: 'ethereum',
  bitcoin: 'ethereum'
};

/**
 * Cross-Chain Error Handler class
 */
class CrossChainErrorHandler {
  // Track chain availability status
  private chainAvailability: Record<BlockchainType, {
    isAvailable: boolean;
    lastCheck: number;
    consecutiveFailures: number;
    recoveryAttempts: number;
  }> = {
    ethereum: { isAvailable: true, lastCheck: Date.now(), consecutiveFailures: 0, recoveryAttempts: 0 },
    solana: { isAvailable: true, lastCheck: Date.now(), consecutiveFailures: 0, recoveryAttempts: 0 },
    ton: { isAvailable: true, lastCheck: Date.now(), consecutiveFailures: 0, recoveryAttempts: 0 },
    bitcoin: { isAvailable: true, lastCheck: Date.now(), consecutiveFailures: 0, recoveryAttempts: 0 }
  };

  /**
   * Analyze and categorize an error
   */
  public analyze(error: any, context: ErrorContext): CrossChainError {
    // Extract useful information from the error
    const errorMessage = this.extractErrorMessage(error);
    const blockchain = context.blockchain;
    
    // Update chain availability tracking if this is a connection error
    if (blockchain && 
        (errorMessage.includes('connection') || 
         errorMessage.includes('timeout') || 
         errorMessage.includes('unavailable'))) {
      this.updateChainAvailability(blockchain, false);
    }
    
    // Try to match against known error patterns for this blockchain
    if (blockchain) {
      const patterns = errorPatterns[blockchain] || [];
      
      for (const pattern of patterns) {
        if (pattern.pattern.test(errorMessage)) {
          // Return categorized error with the matched pattern
          return {
            originalError: error,
            message: errorMessage,
            category: pattern.category,
            blockchain,
            recoverable: pattern.recoverable,
            solution: pattern.solution,
            retryStrategy: pattern.recoverable 
              ? defaultRetryStrategies[pattern.category]
              : undefined,
            metadata: {
              ...context.metadata,
              chainAvailability: this.chainAvailability[blockchain]
            }
          };
        }
      }
      
      // Check if the chain might be unavailable based on our tracking
      if (this.isChainPotentiallyUnavailable(blockchain)) {
        return {
          originalError: error,
          message: `${blockchain} chain appears to be unavailable: ${errorMessage}`,
          category: CrossChainErrorCategory.CHAIN_UNAVAILABLE,
          blockchain,
          recoverable: true,
          solution: `Switch to fallback chain: ${fallbackChains[blockchain]}`,
          retryStrategy: defaultRetryStrategies[CrossChainErrorCategory.CHAIN_UNAVAILABLE],
          metadata: {
            ...context.metadata,
            chainAvailability: this.chainAvailability[blockchain],
            suggestedFallbackChain: fallbackChains[blockchain]
          }
        };
      }
    }
    
    // If no specific match was found, use the context category if provided
    if (context.category) {
      return {
        originalError: error,
        message: errorMessage,
        category: context.category,
        blockchain,
        recoverable: defaultRetryStrategies[context.category].shouldRetry,
        retryStrategy: defaultRetryStrategies[context.category],
        metadata: context.metadata
      };
    }
    
    // Default to unknown error category if no match and no context category
    return {
      originalError: error,
      message: errorMessage,
      category: CrossChainErrorCategory.UNKNOWN,
      blockchain,
      recoverable: true,
      retryStrategy: defaultRetryStrategies[CrossChainErrorCategory.UNKNOWN],
      metadata: context.metadata
    };
  }
  
  /**
   * Handle an error with the specified context
   */
  public handle(error: any, context: ErrorContext): CrossChainError {
    // First analyze the error
    const analyzedError = this.analyze(error, context);
    
    // Log the error with appropriate security event level
    this.logError(analyzedError, context);
    
    // Apply blockchain-specific adjustments
    this.applyBlockchainSpecificAdjustments(analyzedError);
    
    // For recoverable errors, provide alternative endpoints if available
    if (analyzedError.recoverable && analyzedError.blockchain && 
        analyzedError.category === CrossChainErrorCategory.CONNECTION_FAILURE) {
      analyzedError.retryStrategy = {
        ...analyzedError.retryStrategy as RetryStrategy,
        alternativeEndpoint: this.getAlternativeEndpoint(analyzedError.blockchain)
      };
    }
    
    // For certain serious errors, suggest fallback to another chain
    if (analyzedError.category === CrossChainErrorCategory.VALIDATION_FAILURE && 
        analyzedError.blockchain) {
      analyzedError.retryStrategy = {
        ...analyzedError.retryStrategy as RetryStrategy,
        fallbackChain: fallbackChains[analyzedError.blockchain]
      };
    }
    
    return analyzedError;
  }
  
  /**
   * Extract a clean error message from any error type
   */
  private extractErrorMessage(error: any): string {
    if (typeof error === 'string') {
      return error;
    }
    
    if (error instanceof Error) {
      return error.message;
    }
    
    // Some blockchain libraries wrap errors in specific formats
    if (error?.reason) return error.reason;
    if (error?.message) return error.message;
    if (error?.error?.message) return error.error.message;
    if (error?.data?.message) return error.data.message;
    
    // JSON stringify as fallback
    try {
      return JSON.stringify(error);
    } catch {
      return 'Unknown error';
    }
  }
  
  /**
   * Log error with appropriate severity level
   */
  private logError(error: CrossChainError, context: ErrorContext): void {
    const logData = {
      errorCategory: error.category,
      errorMessage: error.message,
      blockchain: error.blockchain,
      operation: context.operation,
      retryCount: context.retryCount,
      vaultId: context.vaultId,
      transactionId: context.transactionId,
      recoverable: error.recoverable,
      metadata: {
        ...error.metadata,
        ...context.metadata
      }
    };
    
    // Determine log level based on error category and recoverability
    switch (error.category) {
      case CrossChainErrorCategory.CONNECTION_FAILURE:
      case CrossChainErrorCategory.RATE_LIMIT_EXCEEDED:
      case CrossChainErrorCategory.NODE_SYNCING:
        if (error.recoverable) {
          securityLogger.info(`Recoverable ${error.category} in ${error.blockchain}`, logData);
        } else {
          securityLogger.warn(`Non-recoverable ${error.category} in ${error.blockchain}`, logData);
        }
        break;
        
      case CrossChainErrorCategory.TRANSACTION_FAILURE:
      case CrossChainErrorCategory.VERIFICATION_FAILURE:
        if (error.recoverable) {
          securityLogger.warn(`Recoverable ${error.category} in ${error.blockchain}`, logData);
        } else {
          securityLogger.error(`Non-recoverable ${error.category} in ${error.blockchain}`, logData);
        }
        break;
        
      case CrossChainErrorCategory.UNAUTHORIZED_ACCESS:
        securityLogger.critical(`Security incident: ${error.category}`, logData);
        break;
        
      default:
        securityLogger.error(`Error in ${error.blockchain || 'unknown'} blockchain: ${error.message}`, logData);
    }
  }
  
  /**
   * Apply blockchain-specific adjustments to error handling
   */
  private applyBlockchainSpecificAdjustments(error: CrossChainError): void {
    // Skip if no blockchain specified
    if (!error.blockchain) return;
    
    // Apply blockchain-specific adjustments
    switch (error.blockchain) {
      case 'ethereum':
        // For Ethereum gas-related errors, adjust retry strategy
        if (error.message.includes('gas') && error.recoverable) {
          error.retryStrategy = {
            ...error.retryStrategy as RetryStrategy,
            delayMs: 15000, // Longer delay for gas issues
            maxRetries: 5   // More retries for gas issues
          };
        }
        break;
        
      case 'solana':
        // For Solana blockhash expired errors, adjust retry strategy
        if (error.message.includes('blockhash') && error.recoverable) {
          error.retryStrategy = {
            ...error.retryStrategy as RetryStrategy,
            delayMs: 1000,  // Shorter delay for blockhash refresh
            maxRetries: 3
          };
        }
        break;
        
      case 'ton':
        // TON-specific adjustments
        if (error.message.includes('fee') && error.recoverable) {
          error.retryStrategy = {
            ...error.retryStrategy as RetryStrategy,
            delayMs: 5000,
            maxRetries: 2
          };
        }
        break;
        
      case 'bitcoin':
        // Bitcoin-specific adjustments
        if (error.message.includes('fee') && error.recoverable) {
          error.retryStrategy = {
            ...error.retryStrategy as RetryStrategy,
            delayMs: 60000, // Bitcoin needs longer delays between retries
            maxRetries: 3
          };
        }
        break;
    }
  }
  
  /**
   * Get alternative endpoint for a blockchain
   */
  private getAlternativeEndpoint(blockchain: BlockchainType): string | undefined {
    // In a real implementation, this would return actual alternative endpoints
    // For now, just return placeholder values
    switch (blockchain) {
      case 'ethereum':
        return config.getAlternativeEndpoint('ethereum');
      case 'solana':
        return config.getAlternativeEndpoint('solana');
      case 'ton':
        return config.getAlternativeEndpoint('ton');
      case 'bitcoin':
        return config.getAlternativeEndpoint('bitcoin');
      default:
        return undefined;
    }
  }

  /**
   * Update chain availability status
   */
  public updateChainAvailability(chain: BlockchainType, isAvailable: boolean): void {
    const status = this.chainAvailability[chain];
    status.lastCheck = Date.now();
    
    if (isAvailable) {
      // Reset failure count on successful connection
      status.isAvailable = true;
      status.consecutiveFailures = 0;
      securityLogger.info(`Chain ${chain} is now available`, { chain });
    } else {
      // Increment failure count
      status.consecutiveFailures++;
      
      // Mark as unavailable after 3 consecutive failures
      if (status.consecutiveFailures >= 3) {
        const wasAvailable = status.isAvailable;
        status.isAvailable = false;
        
        if (wasAvailable) {
          securityLogger.warn(`Chain ${chain} is now marked as unavailable after ${status.consecutiveFailures} consecutive failures`, { 
            chain, 
            consecutiveFailures: status.consecutiveFailures,
            timeSinceLastSuccess: Date.now() - status.lastCheck
          });
        }
      }
    }
  }

  /**
   * Check if a chain is potentially unavailable based on consecutive failures
   */
  private isChainPotentiallyUnavailable(chain: BlockchainType): boolean {
    const status = this.chainAvailability[chain];
    return status.consecutiveFailures >= 3;
  }

  /**
   * Get recommended fallback chain
   */
  public getRecommendedFallbackChain(primaryChain: BlockchainType): BlockchainType | undefined {
    // If primary chain is available, no fallback needed
    if (this.chainAvailability[primaryChain].isAvailable) {
      return undefined;
    }
    
    // Get the configured fallback chain
    const fallbackChain = fallbackChains[primaryChain];
    
    // If fallback is also unavailable, try to find any available chain
    if (!this.chainAvailability[fallbackChain].isAvailable) {
      for (const chain of Object.keys(this.chainAvailability) as BlockchainType[]) {
        if (this.chainAvailability[chain].isAvailable && chain !== primaryChain) {
          return chain;
        }
      }
      
      // If all chains are unavailable, return the configured fallback anyway
      return fallbackChain;
    }
    
    return fallbackChain;
  }

  /**
   * Determine if partial verification should be accepted
   * This method helps decide whether to accept a partial verification result
   * when some chains are unavailable
   */
  public shouldAcceptPartialVerification(
    primaryChain: BlockchainType,
    availableChains: BlockchainType[],
    requiredChainsCount: number
  ): { shouldAccept: boolean; reason: string } {
    // If primary chain is unavailable, we typically shouldn't accept
    if (!this.chainAvailability[primaryChain].isAvailable) {
      return { 
        shouldAccept: false, 
        reason: `Primary chain ${primaryChain} is unavailable` 
      };
    }
    
    // Count how many chains are available
    const availableChainCount = availableChains.filter(
      chain => this.chainAvailability[chain].isAvailable
    ).length;
    
    // If we have enough chains available, accept the partial verification
    if (availableChainCount >= requiredChainsCount) {
      return { 
        shouldAccept: true, 
        reason: `${availableChainCount} chains available, ${requiredChainsCount} required` 
      };
    }
    
    // Otherwise, reject
    return { 
      shouldAccept: false, 
      reason: `Only ${availableChainCount} chains available, ${requiredChainsCount} required` 
    };
  }

  /**
   * Check if the error is recoverable and we should try again
   */
  public shouldAttemptRecovery(error: CrossChainError): boolean {
    // Skip recovery attempts if explicitly marked as non-recoverable
    if (!error.recoverable) {
      return false;
    }
    
    // Check if we have a retry strategy
    if (!error.retryStrategy) {
      return false;
    }
    
    // Check if we've already tried too many times
    const retryCount = error.metadata?.retryCount || 0;
    if (retryCount >= error.retryStrategy.maxRetries) {
      return false;
    }
    
    // For chain unavailability errors, check if recovery makes sense
    if (error.category === CrossChainErrorCategory.CHAIN_UNAVAILABLE && error.blockchain) {
      const status = this.chainAvailability[error.blockchain];
      
      // If we've already tried recovery multiple times, don't try again
      if (status.recoveryAttempts >= 3) {
        return false;
      }
      
      // Increment recovery attempts
      status.recoveryAttempts++;
    }
    
    return true;
  }
  
  /**
   * Calculate appropriate retry delay based on retry count and strategy
   */
  public calculateRetryDelay(error: CrossChainError, retryCount: number): number {
    const strategy = error.retryStrategy;
    
    if (!strategy || !strategy.shouldRetry) {
      return 0;
    }
    
    // Apply exponential backoff if configured
    if (strategy.exponentialBackoff) {
      return Math.min(
        strategy.delayMs * Math.pow(2, retryCount),
        60000 // Max 1 minute delay
      );
    }
    
    return strategy.delayMs;
  }
  
  /**
   * Determine if another retry should be attempted
   */
  public shouldRetry(error: CrossChainError, currentRetryCount: number): boolean {
    const strategy = error.retryStrategy;
    
    if (!strategy || !strategy.shouldRetry) {
      return false;
    }
    
    return currentRetryCount < strategy.maxRetries;
  }
  
  /**
   * Get suggested fallback chain if available
   */
  public getFallbackChain(error: CrossChainError): BlockchainType | undefined {
    return error.retryStrategy?.fallbackChain;
  }
  
  /**
   * Get suggested solution for this error
   */
  public getSolution(error: CrossChainError): string | undefined {
    return error.solution;
  }
}

// Export singleton instance
export const crossChainErrorHandler = new CrossChainErrorHandler();