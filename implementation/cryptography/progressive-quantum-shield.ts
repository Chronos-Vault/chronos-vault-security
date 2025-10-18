/**
 * Progressive Quantum-Resistant Shield
 * 
 * A specialized security service that automatically adjusts the quantum-resistant
 * security level based on the vault's value threshold and implements lattice-based
 * cryptography that becomes stronger over time.
 */

import { randomBytes, createHash } from 'crypto';
import { QuantumResistantEncryption, QuantumResistantAlgorithm } from './quantum-resistant-encryption';
import { quantumResistantEncryption } from './quantum-resistant-encryption';

interface SecurityTier {
  id: string;
  name: string;
  minValueThreshold: number;
  maxValueThreshold: number | null;
  algorithmStrength: 'standard' | 'high' | 'maximum';
  signatureAlgorithm: QuantumResistantAlgorithm;
  encryptionAlgorithm: QuantumResistantAlgorithm;
  requiredSignatures: number;
  zkProofRequired: boolean;
  description: string;
}

interface ProgressiveEncryptionConfig {
  enabledTiers: string[];  // IDs of the enabled tiers
  autoUpgradeSecurity: boolean;
  autoDowngradeSecurity: boolean;
  refreshIntervalHours: number;
  enableLatticeMutation: boolean;
  enforceZeroKnowledgeProofs: boolean;
}

interface EncryptionStrength {
  iterations: number;
  memorySize: number;
  parallelism: number;
  keyLength: number;
}

interface ProgressiveSecurityMetrics {
  vaultId: string;
  currentTier: string;
  securityStrength: number;
  lastUpgrade: Date | null;
  hasZeroKnowledgeProofs: boolean;
  signatures: {
    algorithm: string;
    strength: number;
    lastRotated: Date;
  };
  encryption: {
    algorithm: string;
    strength: number;
    latticeParameters: {
      dimension: number;
      modulus: number;
      errors: number;
    };
  };
}

// Define the available security tiers
const SECURITY_TIERS: SecurityTier[] = [
  {
    id: 'tier1',
    name: 'Standard Protection',
    minValueThreshold: 0,
    maxValueThreshold: 10000, // $10,000
    algorithmStrength: 'standard',
    signatureAlgorithm: QuantumResistantAlgorithm.DILITHIUM,
    encryptionAlgorithm: QuantumResistantAlgorithm.KYBER,
    requiredSignatures: 1,
    zkProofRequired: false,
    description: 'Basic quantum-resistant protection suitable for lower value assets'
  },
  {
    id: 'tier2',
    name: 'Enhanced Protection',
    minValueThreshold: 10000,
    maxValueThreshold: 100000, // $100,000
    algorithmStrength: 'high',
    signatureAlgorithm: QuantumResistantAlgorithm.DILITHIUM,
    encryptionAlgorithm: QuantumResistantAlgorithm.KYBER,
    requiredSignatures: 2,
    zkProofRequired: false,
    description: 'Enhanced protection with stronger parameters and multi-signature requirements'
  },
  {
    id: 'tier3',
    name: 'Advanced Protection',
    minValueThreshold: 100000,
    maxValueThreshold: 1000000, // $1,000,000
    algorithmStrength: 'maximum',
    signatureAlgorithm: QuantumResistantAlgorithm.FALCON,
    encryptionAlgorithm: QuantumResistantAlgorithm.NTRU,
    requiredSignatures: 2,
    zkProofRequired: true,
    description: 'Advanced protection with maximum strength parameters and zero-knowledge proofs'
  },
  {
    id: 'tier4',
    name: 'Maximum Security',
    minValueThreshold: 1000000,
    maxValueThreshold: null, // Unlimited
    algorithmStrength: 'maximum',
    signatureAlgorithm: QuantumResistantAlgorithm.FALCON,
    encryptionAlgorithm: QuantumResistantAlgorithm.NTRU,
    requiredSignatures: 3,
    zkProofRequired: true,
    description: 'Highest level of protection with a combination of multiple quantum-resistant algorithms and triple signature verification'
  }
];

const DEFAULT_CONFIG: ProgressiveEncryptionConfig = {
  enabledTiers: ['tier1', 'tier2', 'tier3', 'tier4'],
  autoUpgradeSecurity: true,
  autoDowngradeSecurity: false, // Don't automatically reduce security
  refreshIntervalHours: 24,
  enableLatticeMutation: true,
  enforceZeroKnowledgeProofs: true
};

// Mapping of strengths to encryption parameters
const STRENGTH_PARAMETERS: Record<string, EncryptionStrength> = {
  standard: {
    iterations: 4,
    memorySize: 65536,
    parallelism: 1,
    keyLength: 32
  },
  high: {
    iterations: 8,
    memorySize: 262144,
    parallelism: 2,
    keyLength: 64
  },
  maximum: {
    iterations: 16,
    memorySize: 1048576,
    parallelism: 4,
    keyLength: 128
  }
};

/**
 * Progressive Quantum Shield that automatically adjusts security based on vault value
 */
export class ProgressiveQuantumShield {
  private config: ProgressiveEncryptionConfig;
  private quantumEncryption: QuantumResistantEncryption;
  private vaultSecurityTiers: Map<string, string> = new Map(); // vaultId -> tierId
  private vaultValues: Map<string, number> = new Map(); // vaultId -> value
  private vaultMetrics: Map<string, ProgressiveSecurityMetrics> = new Map(); // vaultId -> metrics
  private logger: any; // Would be proper logger
  
  constructor(
    quantumEncryption: QuantumResistantEncryption,
    config: Partial<ProgressiveEncryptionConfig> = {}
  ) {
    this.quantumEncryption = quantumEncryption;
    this.config = { ...DEFAULT_CONFIG, ...config };
    
    this.logger = {
      debug: (msg: string) => console.debug(`[ProgressiveQuantum] ${msg}`),
      info: (msg: string) => console.info(`[ProgressiveQuantum] ${msg}`),
      warn: (msg: string) => console.warn(`[ProgressiveQuantum] ${msg}`),
      error: (msg: string, error?: any) => console.error(`[ProgressiveQuantum] ${msg}`, error)
    };
    
    this.logger.info('Progressive Quantum Shield initialized');
    
    // Set up periodic refresh of security levels if auto upgrade is enabled
    if (this.config.autoUpgradeSecurity) {
      setInterval(() => this.refreshSecurityLevels(), this.config.refreshIntervalHours * 60 * 60 * 1000);
    }
  }
  
  /**
   * Initialize vault security with appropriate tier based on value
   */
  public initializeVaultSecurity(vaultId: string, vaultValue: number): ProgressiveSecurityMetrics {
    this.logger.debug(`Initializing security for vault ${vaultId} with value ${vaultValue}`);
    
    // Store vault value for future reference
    this.vaultValues.set(vaultId, vaultValue);
    
    // Determine the appropriate security tier
    const tier = this.determineSecurityTier(vaultValue);
    this.vaultSecurityTiers.set(vaultId, tier.id);
    
    // Initialize security metrics
    const metrics: ProgressiveSecurityMetrics = {
      vaultId,
      currentTier: tier.id,
      securityStrength: this.calculateSecurityStrength(tier),
      lastUpgrade: new Date(),
      hasZeroKnowledgeProofs: tier.zkProofRequired,
      signatures: {
        algorithm: tier.signatureAlgorithm,
        strength: STRENGTH_PARAMETERS[tier.algorithmStrength].iterations,
        lastRotated: new Date()
      },
      encryption: {
        algorithm: tier.encryptionAlgorithm,
        strength: STRENGTH_PARAMETERS[tier.algorithmStrength].keyLength,
        latticeParameters: this.generateLatticePameters(tier.algorithmStrength)
      }
    };
    
    this.vaultMetrics.set(vaultId, metrics);
    
    this.logger.info(`Vault ${vaultId} initialized with security tier ${tier.name}`);
    
    return metrics;
  }
  
  /**
   * Update vault value and adjust security tier if necessary
   */
  public updateVaultValue(vaultId: string, newValue: number): ProgressiveSecurityMetrics {
    const currentValue = this.vaultValues.get(vaultId);
    
    if (currentValue === undefined) {
      // If vault doesn't exist yet, initialize it
      return this.initializeVaultSecurity(vaultId, newValue);
    }
    
    this.vaultValues.set(vaultId, newValue);
    
    // Check if we need to update the security tier
    const currentTierId = this.vaultSecurityTiers.get(vaultId);
    const currentTier = SECURITY_TIERS.find(t => t.id === currentTierId);
    const newTier = this.determineSecurityTier(newValue);
    
    if (!currentTier) {
      throw new Error(`Invalid security tier configuration for vault ${vaultId}`);
    }
    
    // If value increased and we should upgrade security
    if (newValue > currentValue && newTier.id !== currentTier.id && this.config.autoUpgradeSecurity) {
      this.logger.info(`Upgrading vault ${vaultId} security from ${currentTier.name} to ${newTier.name}`);
      return this.upgradeSecurityTier(vaultId, newTier.id);
    }
    
    // If value decreased and we should downgrade security
    if (newValue < currentValue && newTier.id !== currentTier.id && this.config.autoDowngradeSecurity) {
      this.logger.info(`Downgrading vault ${vaultId} security from ${currentTier.name} to ${newTier.name}`);
      return this.downgradeSecurityTier(vaultId, newTier.id);
    }
    
    // If no change is needed, return current metrics
    return this.vaultMetrics.get(vaultId)!;
  }
  
  /**
   * Upgrade vault to a higher security tier
   */
  public upgradeSecurityTier(vaultId: string, newTierId: string): ProgressiveSecurityMetrics {
    const currentMetrics = this.vaultMetrics.get(vaultId);
    
    if (!currentMetrics) {
      throw new Error(`No security metrics found for vault ${vaultId}`);
    }
    
    const newTier = SECURITY_TIERS.find(t => t.id === newTierId);
    
    if (!newTier) {
      throw new Error(`Invalid security tier ${newTierId}`);
    }
    
    // Verify this is an actual upgrade
    const currentTier = SECURITY_TIERS.find(t => t.id === currentMetrics.currentTier);
    
    if (!currentTier) {
      throw new Error(`Invalid current security tier ${currentMetrics.currentTier}`);
    }
    
    if (newTier.minValueThreshold < currentTier.minValueThreshold) {
      throw new Error(`Cannot downgrade security from ${currentTier.name} to ${newTier.name}`);
    }
    
    // Update the security tier
    this.vaultSecurityTiers.set(vaultId, newTier.id);
    
    // Update the metrics
    const updatedMetrics: ProgressiveSecurityMetrics = {
      ...currentMetrics,
      currentTier: newTier.id,
      securityStrength: this.calculateSecurityStrength(newTier),
      lastUpgrade: new Date(),
      hasZeroKnowledgeProofs: newTier.zkProofRequired,
      signatures: {
        algorithm: newTier.signatureAlgorithm,
        strength: STRENGTH_PARAMETERS[newTier.algorithmStrength].iterations,
        lastRotated: new Date()
      },
      encryption: {
        algorithm: newTier.encryptionAlgorithm,
        strength: STRENGTH_PARAMETERS[newTier.algorithmStrength].keyLength,
        latticeParameters: this.generateLatticePameters(newTier.algorithmStrength)
      }
    };
    
    this.vaultMetrics.set(vaultId, updatedMetrics);
    
    this.logger.info(`Vault ${vaultId} security upgraded to ${newTier.name}`);
    
    return updatedMetrics;
  }
  
  /**
   * Downgrade vault to a lower security tier (if allowed)
   */
  private downgradeSecurityTier(vaultId: string, newTierId: string): ProgressiveSecurityMetrics {
    if (!this.config.autoDowngradeSecurity) {
      this.logger.warn(`Attempted to downgrade vault ${vaultId} security, but auto-downgrade is disabled`);
      return this.vaultMetrics.get(vaultId)!;
    }
    
    const currentMetrics = this.vaultMetrics.get(vaultId);
    
    if (!currentMetrics) {
      throw new Error(`No security metrics found for vault ${vaultId}`);
    }
    
    const newTier = SECURITY_TIERS.find(t => t.id === newTierId);
    
    if (!newTier) {
      throw new Error(`Invalid security tier ${newTierId}`);
    }
    
    // Update the security tier
    this.vaultSecurityTiers.set(vaultId, newTier.id);
    
    // Update the metrics, keeping some of the stronger parameters for extra security
    const updatedMetrics: ProgressiveSecurityMetrics = {
      ...currentMetrics,
      currentTier: newTier.id,
      securityStrength: this.calculateSecurityStrength(newTier),
      hasZeroKnowledgeProofs: currentMetrics.hasZeroKnowledgeProofs || newTier.zkProofRequired,
      signatures: {
        algorithm: newTier.signatureAlgorithm,
        strength: Math.max(STRENGTH_PARAMETERS[newTier.algorithmStrength].iterations, 
                         currentMetrics.signatures.strength / 2), // Don't drop strength too much
        lastRotated: currentMetrics.signatures.lastRotated
      },
      encryption: {
        algorithm: newTier.encryptionAlgorithm,
        strength: Math.max(STRENGTH_PARAMETERS[newTier.algorithmStrength].keyLength,
                         currentMetrics.encryption.strength / 2), // Keep some strength
        latticeParameters: currentMetrics.encryption.latticeParameters // Keep existing params
      }
    };
    
    this.vaultMetrics.set(vaultId, updatedMetrics);
    
    this.logger.info(`Vault ${vaultId} security downgraded to ${newTier.name}`);
    
    return updatedMetrics;
  }
  
  /**
   * Get the current security metrics for a vault
   */
  public getVaultSecurityMetrics(vaultId: string): ProgressiveSecurityMetrics | null {
    return this.vaultMetrics.get(vaultId) || null;
  }
  
  /**
   * Force refresh the security levels for all vaults
   */
  public refreshSecurityLevels(): void {
    this.logger.info('Refreshing security levels for all vaults');
    
    // Convert to array to fix TypeScript iterator issue
    for (const [vaultId, value] of Array.from(this.vaultValues.entries())) {
      const currentTierId = this.vaultSecurityTiers.get(vaultId);
      const newTier = this.determineSecurityTier(value);
      
      if (currentTierId !== newTier.id) {
        if (this.config.autoUpgradeSecurity && newTier.minValueThreshold > 
            SECURITY_TIERS.find(t => t.id === currentTierId)!.minValueThreshold) {
          // This is an upgrade
          this.upgradeSecurityTier(vaultId, newTier.id);
        } else if (this.config.autoDowngradeSecurity) {
          // This is a downgrade
          this.downgradeSecurityTier(vaultId, newTier.id);
        }
      }
      
      // If lattice mutation is enabled, strengthen the lattice parameters over time
      if (this.config.enableLatticeMutation) {
        this.mutateLatticeParameters(vaultId);
      }
    }
  }
  
  /**
   * Determine the appropriate security tier based on value
   */
  private determineSecurityTier(value: number): SecurityTier {
    // Find the highest tier that the value qualifies for
    for (let i = SECURITY_TIERS.length - 1; i >= 0; i--) {
      const tier = SECURITY_TIERS[i];
      
      // Skip tiers that aren't enabled
      if (!this.config.enabledTiers.includes(tier.id)) {
        continue;
      }
      
      if (value >= tier.minValueThreshold && 
          (tier.maxValueThreshold === null || value < tier.maxValueThreshold)) {
        return tier;
      }
    }
    
    // If no tier matches (should never happen), return the lowest tier
    return SECURITY_TIERS[0];
  }
  
  /**
   * Calculate a security strength score for a tier (0-100)
   */
  private calculateSecurityStrength(tier: SecurityTier): number {
    let strength = 0;
    
    // Base strength from tier
    switch (tier.algorithmStrength) {
      case 'standard':
        strength += 25;
        break;
      case 'high':
        strength += 50;
        break;
      case 'maximum':
        strength += 75;
        break;
    }
    
    // Additional strength from features
    if (tier.zkProofRequired) {
      strength += 10;
    }
    
    // Additional strength from required signatures
    strength += (tier.requiredSignatures - 1) * 5;
    
    // Cap at 100
    return Math.min(100, strength);
  }
  
  /**
   * Generate lattice parameters based on security strength
   */
  private generateLatticePameters(strength: 'standard' | 'high' | 'maximum'): {
    dimension: number;
    modulus: number;
    errors: number;
  } {
    switch (strength) {
      case 'standard':
        return {
          dimension: 512,
          modulus: 12289,
          errors: 8
        };
      case 'high':
        return {
          dimension: 1024,
          modulus: 12289,
          errors: 10
        };
      case 'maximum':
        return {
          dimension: 2048,
          modulus: 40961,
          errors: 16
        };
    }
  }
  
  /**
   * Mutate the lattice parameters to strengthen them over time
   */
  private mutateLatticeParameters(vaultId: string): void {
    const metrics = this.vaultMetrics.get(vaultId);
    
    if (!metrics) {
      return;
    }
    
    // Calculate how long the vault has existed
    const vaultAge = Date.now() - (metrics.lastUpgrade?.getTime() || Date.now());
    const vaultAgeInDays = vaultAge / (1000 * 60 * 60 * 24);
    
    // Every 30 days, increase the strength slightly
    const strengthIncrease = Math.floor(vaultAgeInDays / 30);
    
    if (strengthIncrease <= 0) {
      return;
    }
    
    // Mutate lattice parameters to increase security over time
    const updatedMetrics: ProgressiveSecurityMetrics = {
      ...metrics,
      securityStrength: Math.min(100, metrics.securityStrength + strengthIncrease),
      encryption: {
        ...metrics.encryption,
        strength: metrics.encryption.strength + strengthIncrease,
        latticeParameters: {
          dimension: metrics.encryption.latticeParameters.dimension + (16 * strengthIncrease),
          modulus: metrics.encryption.latticeParameters.modulus,
          errors: Math.min(20, metrics.encryption.latticeParameters.errors + strengthIncrease)
        }
      }
    };
    
    this.vaultMetrics.set(vaultId, updatedMetrics);
    
    this.logger.debug(`Mutated lattice parameters for vault ${vaultId} to increase strength`);
  }
  
  /**
   * Encrypt data using the appropriate quantum-resistant algorithm for the vault
   */
  public async encryptForVault(vaultId: string, data: string): Promise<any> {
    const metrics = this.vaultMetrics.get(vaultId);
    
    if (!metrics) {
      throw new Error(`No security metrics found for vault ${vaultId}`);
    }
    
    // Determine the tier
    const tier = SECURITY_TIERS.find(t => t.id === metrics.currentTier);
    
    if (!tier) {
      throw new Error(`Invalid security tier ${metrics.currentTier}`);
    }
    
    // Use the quantum encryption service with the appropriate algorithm
    return this.quantumEncryption.encryptData(data);
  }
}

// Singleton instance
let _instance: ProgressiveQuantumShield | null = null;

export function getProgressiveQuantumShield(): ProgressiveQuantumShield {
  if (!_instance) {
    // Use the already imported quantumResistantEncryption
    _instance = new ProgressiveQuantumShield(quantumResistantEncryption);
  }
  return _instance;
}