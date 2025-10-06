import path from 'path';
import { ContractAnalyzer, ContractAnalysis } from './contract-analyzer';
import { InvariantChecker, ContractInvariants } from './invariant-checker';
import { TheoremGenerator, SecurityTheorem } from './theorem-generator';
import { VerificationReportGenerator, VerificationReport } from './verification-report';

export interface FormalVerificationResult {
  contractName: string;
  analysis: ContractAnalysis;
  invariants: ContractInvariants;
  theorems: SecurityTheorem;
  report: VerificationReport;
  verificationTime: number;
}

export interface VerificationConfig {
  contracts: string[];
  outputDir?: string;
  generateReports?: boolean;
  reportFormat?: 'json' | 'html' | 'markdown';
  verbosity?: 'minimal' | 'standard' | 'detailed' | 'full';
}

export class FormalVerificationService {
  private analyzer: ContractAnalyzer;
  private invariantChecker: InvariantChecker;
  private theoremGenerator: TheoremGenerator;
  private reportGenerator: VerificationReportGenerator;
  private verificationCache: Map<string, FormalVerificationResult>;
  private initialized: boolean = false;
  
  constructor() {
    this.analyzer = new ContractAnalyzer();
    this.invariantChecker = new InvariantChecker();
    this.theoremGenerator = new TheoremGenerator();
    this.reportGenerator = new VerificationReportGenerator();
    this.verificationCache = new Map();
  }
  
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }
    
    console.log('\n╔════════════════════════════════════════════════════════════════════════╗');
    console.log('║         CHRONOS VAULT FORMAL VERIFICATION SYSTEM v1.0                 ║');
    console.log('║         Mathematical Proof of Smart Contract Security                 ║');
    console.log('╚════════════════════════════════════════════════════════════════════════╝\n');
    
    console.log('🚀 Initializing Formal Verification System...\n');
    
    const artifactsPath = path.join(process.cwd(), 'artifacts', 'contracts', 'ethereum');
    
    const contractPaths = {
      CVTBridge: path.join(artifactsPath, 'CVTBridge.sol', 'CVTBridge.json'),
      ChronosVault: path.join(artifactsPath, 'ChronosVault.sol', 'ChronosVault.json'),
      CrossChainBridgeV1: path.join(artifactsPath, 'CrossChainBridgeV1.sol', 'CrossChainBridgeV1.json')
    };
    
    console.log('📚 Loading Contract ABIs...');
    for (const [name, filepath] of Object.entries(contractPaths)) {
      try {
        await this.analyzer.loadContractABI(filepath);
      } catch (error) {
        console.warn(`⚠️  Could not load ${name}: ${error}`);
      }
    }
    
    this.initialized = true;
    console.log('\n✅ Formal Verification System Initialized\n');
  }
  
  async verifyContract(contractName: string): Promise<FormalVerificationResult> {
    console.log('\n' + '═'.repeat(80));
    console.log(`🔬 FORMAL VERIFICATION: ${contractName}`);
    console.log('═'.repeat(80) + '\n');
    
    const startTime = Date.now();
    
    const cached = this.verificationCache.get(contractName);
    if (cached) {
      console.log('✅ Using cached verification result\n');
      return cached;
    }
    
    console.log('STEP 1/4: Contract Analysis');
    const analysis = await this.analyzer.analyzeContract(contractName);
    
    console.log('\nSTEP 2/4: Invariant Checking');
    const invariants = await this.invariantChecker.checkInvariants(analysis);
    
    console.log('\nSTEP 3/4: Theorem Generation & Proof');
    const theorems = await this.theoremGenerator.generateTheorems(
      analysis,
      invariants.invariants
    );
    
    console.log('\nSTEP 4/4: Report Generation');
    const report = await this.reportGenerator.generateReport(
      analysis,
      invariants,
      theorems
    );
    
    const verificationTime = Date.now() - startTime;
    
    const result: FormalVerificationResult = {
      contractName,
      analysis,
      invariants,
      theorems,
      report,
      verificationTime
    };
    
    this.verificationCache.set(contractName, result);
    
    console.log(`\n⏱️  Total Verification Time: ${verificationTime}ms`);
    console.log('═'.repeat(80) + '\n');
    
    return result;
  }
  
  async verifyAllContracts(): Promise<Map<string, FormalVerificationResult>> {
    await this.initialize();
    
    console.log('🔬 Starting Comprehensive Formal Verification\n');
    console.log('Contracts to Verify:');
    console.log('  1. CVTBridge - Cross-chain bridge with validator consensus');
    console.log('  2. ChronosVault - Time-locked vault with ERC4626');
    console.log('  3. CrossChainBridgeV1 - HTLC atomic swap implementation\n');
    
    const contracts = ['CVTBridge', 'ChronosVault', 'CrossChainBridgeV1'];
    const results = new Map<string, FormalVerificationResult>();
    
    for (const contractName of contracts) {
      try {
        const result = await this.verifyContract(contractName);
        results.set(contractName, result);
      } catch (error) {
        console.error(`❌ Verification failed for ${contractName}: ${error}`);
      }
    }
    
    this.printOverallSummary(results);
    
    return results;
  }
  
  private printOverallSummary(results: Map<string, FormalVerificationResult>): void {
    console.log('\n' + '═'.repeat(80));
    console.log('📊 OVERALL VERIFICATION SUMMARY');
    console.log('═'.repeat(80) + '\n');
    
    let totalTheorems = 0;
    let provenTheorems = 0;
    let totalInvariants = 0;
    let holdingInvariants = 0;
    let criticalIssues = 0;
    
    results.forEach((result, contractName) => {
      console.log(`${contractName}:`);
      console.log(`  Security Rating: ${this.getRatingEmoji(result.report.securityRating)} ${result.report.securityRating}`);
      console.log(`  Confidence: ${result.report.overallConfidence}%`);
      console.log(`  Theorems: ${result.theorems.provenTheorems}/${result.theorems.totalProofs}`);
      console.log(`  Invariants: ${result.report.summary.invariantsHolding}/${result.report.summary.totalInvariants}`);
      console.log(`  Critical Issues: ${result.report.summary.criticalIssues}`);
      console.log('');
      
      totalTheorems += result.theorems.totalProofs;
      provenTheorems += result.theorems.provenTheorems;
      totalInvariants += result.report.summary.totalInvariants;
      holdingInvariants += result.report.summary.invariantsHolding;
      criticalIssues += result.report.summary.criticalIssues;
    });
    
    console.log('AGGREGATE STATISTICS:');
    console.log(`  Total Theorems Proven: ${provenTheorems}/${totalTheorems} (${Math.round(provenTheorems/totalTheorems*100)}%)`);
    console.log(`  Total Invariants Holding: ${holdingInvariants}/${totalInvariants} (${Math.round(holdingInvariants/totalInvariants*100)}%)`);
    console.log(`  Total Critical Issues: ${criticalIssues}`);
    console.log('');
    
    if (criticalIssues === 0 && provenTheorems === totalTheorems && holdingInvariants === totalInvariants) {
      console.log('✅ ALL CONTRACTS VERIFIED - NO CRITICAL ISSUES FOUND');
    } else if (criticalIssues > 0) {
      console.log('🚨 CRITICAL ISSUES DETECTED - IMMEDIATE ACTION REQUIRED');
    } else {
      console.log('⚠️  SOME ISSUES DETECTED - REVIEW RECOMMENDATIONS');
    }
    
    console.log('═'.repeat(80) + '\n');
  }
  
  private getRatingEmoji(rating: string): string {
    const emojis: Record<string, string> = {
      'SECURE': '✅',
      'WARNING': '⚠️',
      'VULNERABLE': '❌',
      'CRITICAL': '🚨'
    };
    return emojis[rating] || '❓';
  }
  
  async getVerificationStatus(contractName: string): Promise<{
    verified: boolean;
    confidence: number;
    securityRating: string;
    lastVerified?: Date;
  }> {
    const result = this.verificationCache.get(contractName);
    
    if (!result) {
      return {
        verified: false,
        confidence: 0,
        securityRating: 'UNKNOWN'
      };
    }
    
    return {
      verified: true,
      confidence: result.report.overallConfidence,
      securityRating: result.report.securityRating,
      lastVerified: result.report.generatedAt
    };
  }
  
  async exportReports(format: 'json' | 'html' | 'markdown' = 'json'): Promise<Map<string, string>> {
    const exports = new Map<string, string>();
    
    for (const [contractName, result] of this.verificationCache.entries()) {
      const exportData = await this.reportGenerator.exportReport(result.report.reportId, {
        format,
        includeProofSteps: true,
        includeCodeSnippets: false,
        verbosity: 'detailed'
      });
      
      exports.set(contractName, exportData);
    }
    
    return exports;
  }
  
  clearCache(): void {
    this.verificationCache.clear();
    console.log('🗑️  Verification cache cleared');
  }
  
  getAnalyzer(): ContractAnalyzer {
    return this.analyzer;
  }
  
  getInvariantChecker(): InvariantChecker {
    return this.invariantChecker;
  }
  
  getTheoremGenerator(): TheoremGenerator {
    return this.theoremGenerator;
  }
  
  getReportGenerator(): VerificationReportGenerator {
    return this.reportGenerator;
  }
}

export const formalVerificationService = new FormalVerificationService();

export {
  ContractAnalyzer,
  InvariantChecker,
  TheoremGenerator,
  VerificationReportGenerator
};

export type {
  ContractAnalysis,
  ContractInvariants,
  SecurityTheorem,
  VerificationReport
};
