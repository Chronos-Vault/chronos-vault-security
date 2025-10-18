/**
 * Circuit Breaker Monitor Service
 * Monitors live status of V3 circuit breakers on Arbitrum Sepolia
 */

import { ethers } from 'ethers';

// V3 Contract addresses on Arbitrum Sepolia
const CONTRACTS = {
  CROSS_CHAIN_BRIDGE_V3: '0x39601883CD9A115Aba0228fe0620f468Dc710d54',
  CVT_BRIDGE_V3: '0x00d02550f2a8Fd2CeCa0d6b7882f05Beead1E5d0',
  EMERGENCY_MULTISIG: '0xFafCA23a7c085A842E827f53A853141C8243F924'
};

// ABI for CrossChainBridgeV3
const CROSS_CHAIN_BRIDGE_ABI = [
  'function getCircuitBreakerStatus() view returns (bool active, bool emergencyPause, uint256 triggeredAt, string reason, uint256 resumeChainConsensus)',
  'function emergencyController() view returns (address)',
  'function VOLUME_SPIKE_THRESHOLD() view returns (uint256)',
  'function MAX_FAILED_PROOF_RATE() view returns (uint256)',
  'function AUTO_RECOVERY_DELAY() view returns (uint256)'
];

// ABI for CVTBridgeV3
const CVT_BRIDGE_ABI = [
  'function getCircuitBreakerStatus() view returns (bool active, bool emergencyPause, uint256 triggeredAt, string reason, uint256 validatorApprovals)',
  'function emergencyController() view returns (address)',
  'function VOLUME_SPIKE_THRESHOLD() view returns (uint256)',
  'function MAX_FAILED_SIG_RATE() view returns (uint256)',
  'function AUTO_RECOVERY_DELAY() view returns (uint256)'
];

const MULTISIG_ABI = [
  'function REQUIRED_SIGNATURES() view returns (uint256)',
  'function signer1() view returns (address)',
  'function signer2() view returns (address)',
  'function signer3() view returns (address)',
  'function TIME_LOCK_DELAY() view returns (uint256)',
  'function proposalCount() view returns (uint256)'
];

interface CircuitBreakerStatus {
  active: boolean;
  emergencyPause: boolean;
  triggeredAt: number;
  reason: string;
  resumeChainConsensus: number;
  volumeThreshold: string;
  failureRateLimit: string;
  autoRecoveryDelay: string;
}

interface EmergencyControllerStatus {
  address: string;
  requiredSignatures: number;
  timelock: string;
  owners: string[];
}

class CircuitBreakerMonitor {
  private provider: ethers.JsonRpcProvider;
  private crossChainBridgeContract: ethers.Contract;
  private cvtBridgeContract: ethers.Contract;
  private emergencyMultisigContract: ethers.Contract;

  constructor() {
    // Connect to Arbitrum Sepolia
    const rpcUrl = process.env.ARBITRUM_RPC_URL || 'https://sepolia-rollup.arbitrum.io/rpc';
    this.provider = new ethers.JsonRpcProvider(rpcUrl);

    // Initialize contract instances
    this.crossChainBridgeContract = new ethers.Contract(
      CONTRACTS.CROSS_CHAIN_BRIDGE_V3,
      CROSS_CHAIN_BRIDGE_ABI,
      this.provider
    );

    this.cvtBridgeContract = new ethers.Contract(
      CONTRACTS.CVT_BRIDGE_V3,
      CVT_BRIDGE_ABI,
      this.provider
    );

    this.emergencyMultisigContract = new ethers.Contract(
      CONTRACTS.EMERGENCY_MULTISIG,
      MULTISIG_ABI,
      this.provider
    );
  }

  /**
   * Get CrossChainBridgeV3 circuit breaker status
   */
  async getCrossChainBridgeStatus(): Promise<CircuitBreakerStatus> {
    try {
      const [active, emergencyPause, triggeredAt, reason, resumeChainConsensus] = 
        await this.crossChainBridgeContract.getCircuitBreakerStatus();

      const volumeThreshold = await this.crossChainBridgeContract.VOLUME_SPIKE_THRESHOLD();
      const failureRateLimit = await this.crossChainBridgeContract.MAX_FAILED_PROOF_RATE();
      const autoRecoveryDelay = await this.crossChainBridgeContract.AUTO_RECOVERY_DELAY();

      return {
        active,
        emergencyPause,
        triggeredAt: Number(triggeredAt),
        reason,
        resumeChainConsensus: Number(resumeChainConsensus),
        volumeThreshold: volumeThreshold.toString() + '%',
        failureRateLimit: failureRateLimit.toString() + '%',
        autoRecoveryDelay: this.formatDelay(Number(autoRecoveryDelay))
      };
    } catch (error) {
      console.error('Failed to fetch CrossChainBridgeV3 status:', error);
      throw new Error('Circuit breaker status unavailable');
    }
  }

  /**
   * Get CVTBridgeV3 circuit breaker status
   */
  async getCVTBridgeStatus(): Promise<CircuitBreakerStatus> {
    try {
      const [active, emergencyPause, triggeredAt, reason, validatorApprovals] = 
        await this.cvtBridgeContract.getCircuitBreakerStatus();

      const volumeThreshold = await this.cvtBridgeContract.VOLUME_SPIKE_THRESHOLD();
      const failureRateLimit = await this.cvtBridgeContract.MAX_FAILED_SIG_RATE();
      const autoRecoveryDelay = await this.cvtBridgeContract.AUTO_RECOVERY_DELAY();

      return {
        active,
        emergencyPause,
        triggeredAt: Number(triggeredAt),
        reason,
        resumeChainConsensus: Number(validatorApprovals),
        volumeThreshold: volumeThreshold.toString() + '%',
        failureRateLimit: failureRateLimit.toString() + '%',
        autoRecoveryDelay: this.formatDelay(Number(autoRecoveryDelay))
      };
    } catch (error) {
      console.error('Failed to fetch CVTBridgeV3 status:', error);
      throw new Error('Circuit breaker status unavailable');
    }
  }

  /**
   * Get EmergencyMultiSig status
   */
  async getEmergencyControllerStatus(): Promise<EmergencyControllerStatus> {
    try {
      const required = await this.emergencyMultisigContract.REQUIRED_SIGNATURES();
      const timeLockDelay = await this.emergencyMultisigContract.TIME_LOCK_DELAY();

      // Fetch the 3 signer addresses
      const [signer1, signer2, signer3] = await Promise.all([
        this.emergencyMultisigContract.signer1(),
        this.emergencyMultisigContract.signer2(),
        this.emergencyMultisigContract.signer3()
      ]);

      return {
        address: CONTRACTS.EMERGENCY_MULTISIG,
        requiredSignatures: Number(required),
        timelock: this.formatDelay(Number(timeLockDelay)),
        owners: [signer1, signer2, signer3]
      };
    } catch (error) {
      console.error('Failed to fetch EmergencyMultiSig status:', error);
      return {
        address: CONTRACTS.EMERGENCY_MULTISIG,
        requiredSignatures: 2,
        timelock: '48h',
        owners: []
      };
    }
  }

  /**
   * Get combined status for all V3 contracts
   */
  async getAllStatus() {
    try {
      const [crossChainStatus, cvtBridgeStatus, emergencyController] = await Promise.all([
        this.getCrossChainBridgeStatus(),
        this.getCVTBridgeStatus(),
        this.getEmergencyControllerStatus()
      ]);

      return {
        success: true,
        data: {
          crossChainBridge: {
            contract: CONTRACTS.CROSS_CHAIN_BRIDGE_V3,
            ...crossChainStatus
          },
          cvtBridge: {
            contract: CONTRACTS.CVT_BRIDGE_V3,
            ...cvtBridgeStatus
          },
          emergencyController: emergencyController,
          network: 'Arbitrum Sepolia',
          timestamp: Date.now()
        }
      };
    } catch (error: any) {
      return {
        success: false,
        error: error.message || 'Failed to fetch circuit breaker status'
      };
    }
  }

  /**
   * Format delay in seconds to human-readable string
   */
  private formatDelay(seconds: number): string {
    const hours = seconds / 3600;
    if (hours >= 1) {
      return `${hours}h`;
    }
    const minutes = seconds / 60;
    return `${minutes}m`;
  }
}

export const circuitBreakerMonitor = new CircuitBreakerMonitor();
