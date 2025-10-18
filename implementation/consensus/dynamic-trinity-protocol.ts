interface TrinityRoles {
  primary: 'ethereum' | 'solana' | 'ton';
  verifier1: 'ethereum' | 'solana' | 'ton';
  verifier2: 'ethereum' | 'solana' | 'ton';
}

interface TrinityConfig {
  roles: TrinityRoles;
  description: string;
  primaryResponsibilities: string[];
  verifierResponsibilities: string[];
  securityLevel: number;
}

export class DynamicTrinityProtocol {
  
  assignRoles(primaryChain: 'ethereum' | 'solana' | 'ton'): TrinityConfig {
    let roles: TrinityRoles;
    
    switch (primaryChain) {
      case 'ethereum':
        roles = {
          primary: 'ethereum',
          verifier1: 'solana',
          verifier2: 'ton'
        };
        break;
      
      case 'solana':
        roles = {
          primary: 'solana',
          verifier1: 'ethereum',
          verifier2: 'ton'
        };
        break;
      
      case 'ton':
        roles = {
          primary: 'ton',
          verifier1: 'ethereum',
          verifier2: 'solana'
        };
        break;
      
      default:
        roles = {
          primary: 'ethereum',
          verifier1: 'solana',
          verifier2: 'ton'
        };
    }

    return {
      roles,
      description: this.getRoleDescription(roles),
      primaryResponsibilities: this.getPrimaryResponsibilities(),
      verifierResponsibilities: this.getVerifierResponsibilities(),
      securityLevel: 3
    };
  }

  validateTrinityRoles(roles: TrinityRoles): boolean {
    const chains = [roles.primary, roles.verifier1, roles.verifier2];
    
    const uniqueChains = new Set(chains);
    if (uniqueChains.size !== 3) {
      console.error('Trinity Protocol requires 3 different blockchains');
      return false;
    }

    const validChains = ['ethereum', 'solana', 'ton'];
    const allValid = chains.every(chain => validChains.includes(chain));
    
    if (!allValid) {
      console.error('Invalid blockchain in Trinity roles');
      return false;
    }

    return true;
  }

  requiresVerification(
    primaryChain: string,
    securityLevel: number
  ): { ethereum: boolean; solana: boolean; ton: boolean } {
    if (securityLevel < 3) {
      return { ethereum: false, solana: false, ton: false };
    }

    const verification = {
      ethereum: primaryChain !== 'ethereum',
      solana: primaryChain !== 'solana',
      ton: primaryChain !== 'ton'
    };

    return verification;
  }

  async verifyTwoOfThree(
    verifications: { ethereum: boolean; solana: boolean; ton: boolean },
    primaryChain: 'ethereum' | 'solana' | 'ton'
  ): Promise<{ verified: boolean; verifiedChains: string[] }> {
    const verifiedChains: string[] = [];
    
    if (verifications.ethereum) verifiedChains.push('ethereum');
    if (verifications.solana) verifiedChains.push('solana');
    if (verifications.ton) verifiedChains.push('ton');

    const verified = verifiedChains.filter(chain => chain !== primaryChain).length >= 2;

    return {
      verified,
      verifiedChains
    };
  }

  getContractDeploymentPriority(roles: TrinityRoles): {
    priority: string[];
    explanation: string;
  } {
    return {
      priority: [
        roles.primary,
        roles.verifier1,
        roles.verifier2
      ],
      explanation: `Deploy on ${roles.primary} first (holds vault), then ${roles.verifier1} and ${roles.verifier2} for verification`
    };
  }

  calculateFeeSavings(
    primaryChain: 'ethereum' | 'solana' | 'ton',
    feeData: {
      ethereum: number;
      solana: number;
      ton: number;
    }
  ): {
    selectedFee: number;
    vsEthereum: number;
    percentSaved: number;
  } {
    const selectedFee = feeData[primaryChain];
    const ethereumFee = feeData.ethereum;
    const savings = ethereumFee - selectedFee;
    const percentSaved = (savings / ethereumFee) * 100;

    return {
      selectedFee,
      vsEthereum: savings,
      percentSaved: Math.max(0, percentSaved)
    };
  }

  private getRoleDescription(roles: TrinityRoles): string {
    return `Trinity Protocol: ${roles.primary.toUpperCase()} (Primary Vault) + ${roles.verifier1.toUpperCase()} & ${roles.verifier2.toUpperCase()} (2-of-3 Verification)`;
  }

  private getPrimaryResponsibilities(): string[] {
    return [
      'Hold vault smart contract',
      'Store encrypted vault assets',
      'Execute time-lock logic',
      'Process withdrawals after unlock',
      'Emit vault state events'
    ];
  }

  private getVerifierResponsibilities(): string[] {
    return [
      'Monitor primary chain state',
      'Verify vault transactions',
      'Provide 2-of-3 consensus',
      'Enable emergency recovery',
      'Cross-chain state synchronization'
    ];
  }

  generateTrinityMetadata(
    primaryChain: 'ethereum' | 'solana' | 'ton',
    estimatedFees: {
      ethereum: string;
      solana: string;
      ton: string;
    }
  ): {
    roles: TrinityRoles;
    chainInfo: Record<string, any>;
    securityModel: string;
  } {
    const config = this.assignRoles(primaryChain);
    
    const chainInfo = {
      [config.roles.primary]: {
        role: 'primary',
        responsibility: 'Vault Holder',
        estimatedFee: estimatedFees[config.roles.primary],
        priority: 1
      },
      [config.roles.verifier1]: {
        role: 'verifier',
        responsibility: 'Security Verification',
        estimatedFee: estimatedFees[config.roles.verifier1],
        priority: 2
      },
      [config.roles.verifier2]: {
        role: 'verifier',
        responsibility: 'Security Verification',
        estimatedFee: estimatedFees[config.roles.verifier2],
        priority: 3
      }
    };

    return {
      roles: config.roles,
      chainInfo,
      securityModel: 'Trinity Protocol - Mathematical 2-of-3 Consensus'
    };
  }
}

export const dynamicTrinityProtocol = new DynamicTrinityProtocol();

export type { TrinityRoles, TrinityConfig };
