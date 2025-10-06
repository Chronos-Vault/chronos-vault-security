import crypto from 'crypto';
import { quantumCrypto } from './quantum-resistant-crypto';
import { zkProofSystem } from './zk-proof-system';
import { trinityProtocol } from './trinity-protocol';
import { securityLogger, SecurityEventType} from '../monitoring/security-logger';

interface SecurityCheck {
  id: string;
  name: string;
  severity: 'CRITICAL' | 'HIGH' | 'MEDIUM' | 'LOW';
  status: 'PASS' | 'FAIL' | 'WARNING';
  description: string;
  details?: string;
  timestamp: number;
}

interface AuditReport {
  timestamp: number;
  overallStatus: 'SECURE' | 'WARNING' | 'VULNERABLE';
  checks: SecurityCheck[];
  score: number;
  criticalIssues: number;
  highIssues: number;
  mediumIssues: number;
  lowIssues: number;
  recommendations: string[];
}

interface ThreatDetection {
  threatId: string;
  type: 'UNAUTHORIZED_ACCESS' | 'CONSENSUS_MANIPULATION' | 'REPLAY_ATTACK' | 'TIMING_ATTACK' | 'QUANTUM_ATTACK';
  severity: 'CRITICAL' | 'HIGH' | 'MEDIUM' | 'LOW';
  detected: number;
  blocked: boolean;
  details: string;
}

export class AutomatedSecurityAudit {
  private auditHistory: AuditReport[] = [];
  private threatDetections: ThreatDetection[] = [];
  private lastAuditTime: number = 0;
  private readonly AUDIT_INTERVAL = 3600000; // 1 hour
  
  constructor() {}
  
  async initialize(): Promise<void> {
    console.log('🛡️  Initializing Automated Security Audit System...');
    
    await this.runInitialSecurityChecks();
    
    this.startContinuousMonitoring();
    
    console.log('✅ Security Audit System Initialized');
    console.log('   - Quantum Crypto Health: Monitoring');
    console.log('   - ZK Proof System: Monitoring');
    console.log('   - Trinity Protocol: Monitoring');
    console.log('   - Threat Detection: Active');
  }
  
  private async runInitialSecurityChecks(): Promise<void> {
    const checks: SecurityCheck[] = [];
    
    // Check 1: Quantum Crypto Health
    checks.push(await this.checkQuantumCryptoHealth());
    
    // Check 2: ZK Proof System
    checks.push(await this.checkZKProofSystem());
    
    // Check 3: Trinity Protocol Consensus
    checks.push(await this.checkTrinityConsensus());
    
    // Check 4: Cross-Chain Connectivity
    checks.push(await this.checkCrossChainConnectivity());
    
    // Check 5: Key Management
    checks.push(await this.checkKeyManagement());
    
    // Check 6: Cryptographic Randomness
    checks.push(await this.checkCryptographicRandomness());
    
    const report = this.generateAuditReport(checks);
    this.auditHistory.push(report);
    
    securityLogger.info('🛡️  Initial Security Audit Complete', SecurityEventType.SECURITY_AUDIT);
    securityLogger.info(`   Overall Status: ${report.overallStatus}`, SecurityEventType.SECURITY_AUDIT);
    securityLogger.info(`   Security Score: ${report.score}/100`, SecurityEventType.SECURITY_AUDIT);
  }
  
  private async checkQuantumCryptoHealth(): Promise<SecurityCheck> {
    try {
      const metrics = quantumCrypto.getSecurityMetrics();
      
      if (!metrics.initialized) {
        return {
          id: 'QC-001',
          name: 'Quantum Cryptography Initialization',
          severity: 'CRITICAL',
          status: 'FAIL',
          description: 'Quantum crypto not initialized',
          details: 'System must initialize quantum-resistant cryptography before use',
          timestamp: Date.now()
        };
      }
      
      const healthCheck = await quantumCrypto.healthCheck();
      
      if (!healthCheck) {
        return {
          id: 'QC-002',
          name: 'Quantum Cryptography Health Check',
          severity: 'CRITICAL',
          status: 'FAIL',
          description: 'Quantum crypto health check failed',
          details: 'ML-KEM or Dilithium operations are not functioning correctly',
          timestamp: Date.now()
        };
      }
      
      return {
        id: 'QC-001',
        name: 'Quantum Cryptography',
        severity: 'CRITICAL',
        status: 'PASS',
        description: 'Quantum-resistant cryptography operational',
        details: `ML-KEM-1024 + Dilithium-5 with ${metrics.performance.activeKeys} active keys`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'QC-003',
        name: 'Quantum Cryptography Error',
        severity: 'CRITICAL',
        status: 'FAIL',
        description: 'Quantum crypto check threw exception',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private async checkZKProofSystem(): Promise<SecurityCheck> {
    try {
      const metrics = zkProofSystem.getSecurityMetrics();
      
      return {
        id: 'ZK-001',
        name: 'Zero-Knowledge Proof System',
        severity: 'HIGH',
        status: 'PASS',
        description: 'ZK proof system operational',
        details: `${metrics.performance.storedProofs} cached proofs, ${metrics.performance.cacheHits} cache hits`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'ZK-002',
        name: 'ZK Proof System Error',
        severity: 'HIGH',
        status: 'FAIL',
        description: 'ZK proof system check failed',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private async checkTrinityConsensus(): Promise<SecurityCheck> {
    try {
      const chainHealth = await trinityProtocol.getChainHealthStatus();
      
      const healthyChains = Object.values(chainHealth).filter(h => h.status === 'HEALTHY').length;
      
      if (healthyChains < 2) {
        return {
          id: 'TC-001',
          name: 'Trinity Protocol Consensus',
          severity: 'CRITICAL',
          status: 'FAIL',
          description: 'Insufficient healthy chains for 2-of-3 consensus',
          details: `Only ${healthyChains}/3 chains healthy. Trinity requires at least 2 chains.`,
          timestamp: Date.now()
        };
      }
      
      if (healthyChains === 2) {
        return {
          id: 'TC-002',
          name: 'Trinity Protocol Consensus',
          severity: 'HIGH',
          status: 'WARNING',
          description: 'Operating in degraded mode',
          details: `${healthyChains}/3 chains healthy. System functional but one chain down.`,
          timestamp: Date.now()
        };
      }
      
      return {
        id: 'TC-001',
        name: 'Trinity Protocol Consensus',
        severity: 'CRITICAL',
        status: 'PASS',
        description: 'All chains operational',
        details: `${healthyChains}/3 chains healthy. 2-of-3 consensus fully operational.`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'TC-003',
        name: 'Trinity Protocol Error',
        severity: 'CRITICAL',
        status: 'FAIL',
        description: 'Trinity protocol check failed',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private async checkCrossChainConnectivity(): Promise<SecurityCheck> {
    try {
      const chainHealth = await trinityProtocol.getChainHealthStatus();
      
      const connectedChains = Object.entries(chainHealth)
        .filter(([_, health]) => health.status === 'HEALTHY')
        .map(([chain, _]) => chain);
      
      return {
        id: 'CC-001',
        name: 'Cross-Chain Connectivity',
        severity: 'HIGH',
        status: connectedChains.length === 3 ? 'PASS' : 'WARNING',
        description: `${connectedChains.length}/3 chains connected`,
        details: `Connected: ${connectedChains.join(', ')}`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'CC-002',
        name: 'Cross-Chain Connectivity Error',
        severity: 'HIGH',
        status: 'FAIL',
        description: 'Cross-chain connectivity check failed',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private async checkKeyManagement(): Promise<SecurityCheck> {
    try {
      const metrics = quantumCrypto.getSecurityMetrics();
      
      if (metrics.performance.activeKeys < 5) {
        return {
          id: 'KM-001',
          name: 'Key Pool Management',
          severity: 'MEDIUM',
          status: 'WARNING',
          description: 'Key pool below threshold',
          details: `Only ${metrics.performance.activeKeys} keys in pool. Recommend minimum 10.`,
          timestamp: Date.now()
        };
      }
      
      return {
        id: 'KM-001',
        name: 'Key Pool Management',
        severity: 'MEDIUM',
        status: 'PASS',
        description: 'Key pool healthy',
        details: `${metrics.performance.activeKeys} keys available for operations`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'KM-002',
        name: 'Key Management Error',
        severity: 'HIGH',
        status: 'FAIL',
        description: 'Key management check failed',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private async checkCryptographicRandomness(): Promise<SecurityCheck> {
    try {
      const random1 = crypto.randomBytes(32);
      const random2 = crypto.randomBytes(32);
      
      if (Buffer.compare(random1, random2) === 0) {
        return {
          id: 'CR-001',
          name: 'Cryptographic Randomness',
          severity: 'CRITICAL',
          status: 'FAIL',
          description: 'Random number generator producing identical values',
          details: 'CRITICAL: RNG failure detected. System compromised.',
          timestamp: Date.now()
        };
      }
      
      const entropy = this.calculateEntropy(random1);
      
      if (entropy < 7.0) {
        return {
          id: 'CR-002',
          name: 'Cryptographic Randomness',
          severity: 'HIGH',
          status: 'WARNING',
          description: 'Low entropy detected in random values',
          details: `Entropy: ${entropy.toFixed(2)} bits/byte (expected: >7.5)`,
          timestamp: Date.now()
        };
      }
      
      return {
        id: 'CR-001',
        name: 'Cryptographic Randomness',
        severity: 'CRITICAL',
        status: 'PASS',
        description: 'RNG producing high-quality entropy',
        details: `Entropy: ${entropy.toFixed(2)} bits/byte`,
        timestamp: Date.now()
      };
    } catch (error) {
      return {
        id: 'CR-003',
        name: 'Cryptographic Randomness Error',
        severity: 'CRITICAL',
        status: 'FAIL',
        description: 'Randomness check failed',
        details: error instanceof Error ? error.message : 'Unknown error',
        timestamp: Date.now()
      };
    }
  }
  
  private calculateEntropy(buffer: Buffer): number {
    const frequency: number[] = new Array(256).fill(0);
    
    for (let i = 0; i < buffer.length; i++) {
      frequency[buffer[i]]++;
    }
    
    let entropy = 0;
    const length = buffer.length;
    
    for (let i = 0; i < 256; i++) {
      if (frequency[i] > 0) {
        const p = frequency[i] / length;
        entropy -= p * Math.log2(p);
      }
    }
    
    return entropy;
  }
  
  private generateAuditReport(checks: SecurityCheck[]): AuditReport {
    const criticalIssues = checks.filter(c => c.severity === 'CRITICAL' && c.status === 'FAIL').length;
    const highIssues = checks.filter(c => c.severity === 'HIGH' && c.status === 'FAIL').length;
    const mediumIssues = checks.filter(c => c.severity === 'MEDIUM' && c.status === 'FAIL').length;
    const lowIssues = checks.filter(c => c.severity === 'LOW' && c.status === 'FAIL').length;
    
    const passedChecks = checks.filter(c => c.status === 'PASS').length;
    const totalChecks = checks.length;
    const score = Math.round((passedChecks / totalChecks) * 100);
    
    let overallStatus: 'SECURE' | 'WARNING' | 'VULNERABLE' = 'SECURE';
    if (criticalIssues > 0) {
      overallStatus = 'VULNERABLE';
    } else if (highIssues > 0 || mediumIssues > 0) {
      overallStatus = 'WARNING';
    }
    
    const recommendations: string[] = [];
    
    if (criticalIssues > 0) {
      recommendations.push('URGENT: Address critical security issues immediately');
      recommendations.push('Do not deploy to production until critical issues resolved');
    }
    
    if (highIssues > 0) {
      recommendations.push('Schedule immediate review of high severity issues');
    }
    
    const failedChecks = checks.filter(c => c.status === 'FAIL');
    failedChecks.forEach(check => {
      recommendations.push(`Fix: ${check.name} - ${check.description}`);
    });
    
    if (score === 100) {
      recommendations.push('All security checks passed - system ready for production');
      recommendations.push('Continue monitoring with automated audits');
      recommendations.push('Schedule professional third-party audit before mainnet');
    }
    
    return {
      timestamp: Date.now(),
      overallStatus,
      checks,
      score,
      criticalIssues,
      highIssues,
      mediumIssues,
      lowIssues,
      recommendations
    };
  }
  
  async runFullAudit(): Promise<AuditReport> {
    securityLogger.info('🛡️  Running Full Security Audit...', SecurityEventType.SECURITY_AUDIT);
    
    const checks: SecurityCheck[] = [];
    
    checks.push(await this.checkQuantumCryptoHealth());
    checks.push(await this.checkZKProofSystem());
    checks.push(await this.checkTrinityConsensus());
    checks.push(await this.checkCrossChainConnectivity());
    checks.push(await this.checkKeyManagement());
    checks.push(await this.checkCryptographicRandomness());
    
    const report = this.generateAuditReport(checks);
    this.auditHistory.push(report);
    this.lastAuditTime = Date.now();
    
    securityLogger.info('✅ Security Audit Complete', SecurityEventType.SECURITY_AUDIT);
    securityLogger.info(`   Status: ${report.overallStatus}`, SecurityEventType.SECURITY_AUDIT);
    securityLogger.info(`   Score: ${report.score}/100`, SecurityEventType.SECURITY_AUDIT);
    securityLogger.info(`   Critical: ${report.criticalIssues}, High: ${report.highIssues}, Medium: ${report.mediumIssues}, Low: ${report.lowIssues}`, SecurityEventType.SECURITY_AUDIT);
    
    return report;
  }
  
  private startContinuousMonitoring(): void {
    setInterval(async () => {
      await this.runFullAudit();
    }, this.AUDIT_INTERVAL);
    
    securityLogger.info(`🔄 Continuous monitoring started (interval: ${this.AUDIT_INTERVAL/1000/60} minutes)`, SecurityEventType.SECURITY_AUDIT);
  }
  
  detectThreat(
    type: ThreatDetection['type'],
    severity: ThreatDetection['severity'],
    details: string,
    blocked: boolean
  ): void {
    const threat: ThreatDetection = {
      threatId: `THREAT-${Date.now()}`,
      type,
      severity,
      detected: Date.now(),
      blocked,
      details
    };
    
    this.threatDetections.push(threat);
    
    securityLogger.warn(`🚨 THREAT DETECTED: ${type}`, SecurityEventType.THREAT_DETECTED);
    securityLogger.warn(`   Severity: ${severity}`, SecurityEventType.THREAT_DETECTED);
    securityLogger.warn(`   Blocked: ${blocked ? 'YES ✅' : 'NO ❌'}`, SecurityEventType.THREAT_DETECTED);
    securityLogger.warn(`   Details: ${details}`, SecurityEventType.THREAT_DETECTED);
    
    if (severity === 'CRITICAL' && !blocked) {
      securityLogger.error('⚠️  CRITICAL THREAT NOT BLOCKED - IMMEDIATE ACTION REQUIRED', SecurityEventType.THREAT_DETECTED);
    }
  }
  
  getLatestAuditReport(): AuditReport | null {
    if (this.auditHistory.length === 0) {
      return null;
    }
    return this.auditHistory[this.auditHistory.length - 1];
  }
  
  getThreatHistory(limit: number = 10): ThreatDetection[] {
    return this.threatDetections.slice(-limit).reverse();
  }
  
  getSecurityMetrics() {
    const latestReport = this.getLatestAuditReport();
    
    return {
      audit: {
        lastAuditTime: this.lastAuditTime,
        totalAudits: this.auditHistory.length,
        auditInterval: `${this.AUDIT_INTERVAL/1000/60} minutes`,
        latestScore: latestReport?.score || 0,
        overallStatus: latestReport?.overallStatus || 'UNKNOWN'
      },
      threats: {
        totalDetected: this.threatDetections.length,
        blockedThreats: this.threatDetections.filter(t => t.blocked).length,
        criticalThreats: this.threatDetections.filter(t => t.severity === 'CRITICAL').length,
        recentThreats: this.threatDetections.slice(-5).length
      },
      checks: {
        quantumCrypto: 'Monitored',
        zkProofs: 'Monitored',
        trinityProtocol: 'Monitored',
        crossChainConnectivity: 'Monitored',
        keyManagement: 'Monitored',
        cryptographicRandomness: 'Monitored'
      }
    };
  }
}

export const securityAudit = new AutomatedSecurityAudit();
