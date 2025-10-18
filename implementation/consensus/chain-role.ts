/**
 * Chain Role Definitions
 * 
 * Defines the roles each blockchain plays in the Triple-Chain Security Architecture
 */

export enum ChainRole {
  PRIMARY = 'PRIMARY',
  MONITORING = 'MONITORING',
  RECOVERY = 'RECOVERY',
  FALLBACK = 'FALLBACK'
}

export interface ChainConfiguration {
  chain: string;
  role: ChainRole;
  priority: number;
  isActive: boolean;
  endpoints: string[];
  fallbackEndpoints?: string[];
}

// Default chain configuration based on Triple-Chain Security architecture
export const DEFAULT_CHAIN_CONFIGURATION: Record<string, ChainConfiguration> = {
  ton: {
    chain: 'ton',
    role: ChainRole.PRIMARY,
    priority: 1,
    isActive: true,
    endpoints: ['https://toncenter.com/api/v2/jsonRPC']
  },
  ethereum: {
    chain: 'ethereum',
    role: ChainRole.RECOVERY,
    priority: 3,
    isActive: true,
    endpoints: process.env.ETHEREUM_RPC_URL ? [process.env.ETHEREUM_RPC_URL] : []
  },
  solana: {
    chain: 'solana',
    role: ChainRole.MONITORING,
    priority: 2,
    isActive: true,
    endpoints: process.env.SOLANA_RPC_URL ? [process.env.SOLANA_RPC_URL] : []
  },
  bitcoin: {
    chain: 'bitcoin',
    role: ChainRole.FALLBACK,
    priority: 4,
    isActive: true,
    endpoints: ['https://blockstream.info/api/']
  }
};

export function determineChainRole(chainName: string): ChainRole {
  const config = DEFAULT_CHAIN_CONFIGURATION[chainName.toLowerCase()];
  return config ? config.role : ChainRole.FALLBACK;
}

export function getNextFallbackChain(currentChain: string): string | undefined {
  const currentConfig = DEFAULT_CHAIN_CONFIGURATION[currentChain.toLowerCase()];
  if (!currentConfig) return undefined;
  
  // Find chains with higher priority (lower priority number)
  const availableFallbacks = Object.values(DEFAULT_CHAIN_CONFIGURATION)
    .filter(config => 
      config.priority > currentConfig.priority && 
      config.isActive && 
      config.role !== ChainRole.PRIMARY
    )
    .sort((a, b) => a.priority - b.priority);
    
  return availableFallbacks.length > 0 ? availableFallbacks[0].chain : undefined;
}

export function getPrimaryChain(): string {
  const primaryConfig = Object.values(DEFAULT_CHAIN_CONFIGURATION)
    .find(config => config.role === ChainRole.PRIMARY && config.isActive);
    
  return primaryConfig ? primaryConfig.chain : 'ethereum';
}