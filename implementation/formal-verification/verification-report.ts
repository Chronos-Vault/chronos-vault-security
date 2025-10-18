import { ContractAnalysis, SecurityProperty } from './contract-analyzer';
import { ContractInvariants, InvariantCheckResult } from './invariant-checker';
import { SecurityTheorem, Theorem } from './theorem-generator';

export interface VerificationReport {
  reportId: string;
  contractName: string;
  generatedAt: Date;
  overallConfidence: number;
  securityRating: 'SECURE' | 'WARNING' | 'VULNERABLE' | 'CRITICAL';
  summary: VerificationSummary;
  analysis: ContractAnalysis;
  invariants: ContractInvariants;
  theorems: SecurityTheorem;
  vulnerabilities: Vulnerability[];
  recommendations: Recommendation[];
  proofSummary: ProofSummary;
}

export interface VerificationSummary {
  totalFunctions: number;
  totalInvariants: number;
  invariantsHolding: number;
  invariantsViolated: number;
  totalTheorems: number;
  theoremsProven: number;
  criticalIssues: number;
  highIssues: number;
  mediumIssues: number;
  lowIssues: number;
}

export interface Vulnerability {
  vulnerabilityId: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  title: string;
  description: string;
  affectedFunctions: string[];
  exploitScenario: string;
  recommendation: string;
  cweId?: string;
}

export interface Recommendation {
  recommendationId: string;
  priority: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  title: string;
  description: string;
  implementationSteps: string[];
  expectedImpact: string;
}

export interface ProofSummary {
  totalProofSteps: number;
  proofMethods: {
    symbolicExecution: number;
    theoremProving: number;
    modelChecking: number;
    smtSolver: number;
  };
  verificationTime: number;
  coverageScore: number;
}

export interface ReportExportOptions {
  format: 'json' | 'html' | 'markdown' | 'pdf';
  includeProofSteps: boolean;
  includeCodeSnippets: boolean;
  verbosity: 'minimal' | 'standard' | 'detailed' | 'full';
}

export class VerificationReportGenerator {
  private reports: Map<string, VerificationReport>;
  
  constructor() {
    this.reports = new Map();
  }
  
  async generateReport(
    analysis: ContractAnalysis,
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): Promise<VerificationReport> {
    console.log(`\n📊 Generating Verification Report for ${analysis.contractName}`);
    console.log('━'.repeat(80));
    
    const reportId = `REPORT_${analysis.contractName}_${Date.now()}`;
    
    const summary = this.generateSummary(analysis, invariants, theorems);
    const vulnerabilities = this.identifyVulnerabilities(invariants, theorems);
    const recommendations = this.generateRecommendations(vulnerabilities, invariants);
    const proofSummary = this.generateProofSummary(invariants, theorems);
    const securityRating = this.calculateSecurityRating(summary, vulnerabilities);
    const overallConfidence = this.calculateOverallConfidence(invariants, theorems);
    
    const report: VerificationReport = {
      reportId,
      contractName: analysis.contractName,
      generatedAt: new Date(),
      overallConfidence,
      securityRating,
      summary,
      analysis,
      invariants,
      theorems,
      vulnerabilities,
      recommendations,
      proofSummary
    };
    
    this.reports.set(reportId, report);
    this.printReportSummary(report);
    
    return report;
  }
  
  private generateSummary(
    analysis: ContractAnalysis,
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): VerificationSummary {
    const invariantsHolding = Array.from(invariants.checkResults.values()).filter(r => r.holds).length;
    const invariantsViolated = invariants.invariants.length - invariantsHolding;
    
    let criticalIssues = 0;
    let highIssues = 0;
    let mediumIssues = 0;
    let lowIssues = 0;
    
    invariants.checkResults.forEach(result => {
      if (!result.holds) {
        result.violations.forEach(v => {
          switch (v.severity) {
            case 'critical': criticalIssues++; break;
            case 'high': highIssues++; break;
            case 'medium': mediumIssues++; break;
            case 'low': lowIssues++; break;
          }
        });
      }
    });
    
    return {
      totalFunctions: analysis.functions.length,
      totalInvariants: invariants.invariants.length,
      invariantsHolding,
      invariantsViolated,
      totalTheorems: theorems.totalProofs,
      theoremsProven: theorems.provenTheorems,
      criticalIssues,
      highIssues,
      mediumIssues,
      lowIssues
    };
  }
  
  private identifyVulnerabilities(
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): Vulnerability[] {
    const vulnerabilities: Vulnerability[] = [];
    
    invariants.checkResults.forEach(result => {
      if (!result.holds && result.violations.length > 0) {
        result.violations.forEach(violation => {
          vulnerabilities.push({
            vulnerabilityId: `VULN_${violation.invariant.invariantId}`,
            severity: violation.severity,
            category: violation.invariant.category,
            title: `Invariant Violation: ${violation.invariant.name}`,
            description: violation.invariant.description,
            affectedFunctions: violation.invariant.relatedFunctions,
            exploitScenario: this.generateExploitScenario(violation),
            recommendation: this.generateVulnerabilityRecommendation(violation),
            cweId: this.mapToCWE(violation.invariant.category)
          });
        });
      }
    });
    
    theorems.theorems.forEach(theorem => {
      if (!theorem.proof.verified && theorem.proof.counterExamples.length > 0) {
        vulnerabilities.push({
          vulnerabilityId: `VULN_${theorem.theoremId}`,
          severity: this.theoremSeverity(theorem),
          category: theorem.category,
          title: `Unproven Theorem: ${theorem.name}`,
          description: theorem.statement,
          affectedFunctions: [],
          exploitScenario: `Counter-example found: ${JSON.stringify(theorem.proof.counterExamples[0])}`,
          recommendation: 'Add required security controls',
          cweId: this.mapToCWE(theorem.category)
        });
      }
    });
    
    return vulnerabilities;
  }
  
  private generateExploitScenario(violation: any): string {
    return violation.trace.join(' → ');
  }
  
  private generateVulnerabilityRecommendation(violation: any): string {
    const category = violation.invariant.category;
    
    const recommendations: Record<string, string> = {
      'reentrancy': 'Add nonReentrant modifier and follow Checks-Effects-Interactions pattern',
      'access_control': 'Add appropriate access control modifiers (onlyOwner, onlyValidator, etc.)',
      'state_integrity': 'Ensure state invariants are maintained across all operations',
      'arithmetic': 'Use SafeMath or Solidity 0.8+ with overflow protection',
      'safety': 'Add proper validation and checks for all user inputs',
      'liveness': 'Ensure timeout mechanisms and recovery paths exist'
    };
    
    return recommendations[category] || 'Review and fix the security issue';
  }
  
  private mapToCWE(category: string): string {
    const cweMapping: Record<string, string> = {
      'reentrancy': 'CWE-841',
      'access_control': 'CWE-284',
      'arithmetic': 'CWE-190',
      'state_integrity': 'CWE-703',
      'safety': 'CWE-20',
      'liveness': 'CWE-833'
    };
    
    return cweMapping[category] || 'CWE-Other';
  }
  
  private theoremSeverity(theorem: Theorem): 'critical' | 'high' | 'medium' | 'low' {
    if (theorem.category === 'security') return 'critical';
    if (theorem.category === 'safety') return 'high';
    if (theorem.category === 'correctness') return 'medium';
    return 'low';
  }
  
  private generateRecommendations(
    vulnerabilities: Vulnerability[],
    invariants: ContractInvariants
  ): Recommendation[] {
    const recommendations: Recommendation[] = [];
    
    const criticalVulns = vulnerabilities.filter(v => v.severity === 'critical');
    if (criticalVulns.length > 0) {
      recommendations.push({
        recommendationId: 'REC_001',
        priority: 'critical',
        category: 'Security',
        title: 'Address Critical Security Vulnerabilities',
        description: `Found ${criticalVulns.length} critical security issues that must be fixed immediately`,
        implementationSteps: [
          'Review all critical vulnerabilities',
          'Implement recommended security controls',
          'Re-run formal verification',
          'Conduct security audit'
        ],
        expectedImpact: 'Prevent potential exploits and fund loss'
      });
    }
    
    const hasReentrancy = vulnerabilities.some(v => v.category === 'reentrancy');
    if (hasReentrancy) {
      recommendations.push({
        recommendationId: 'REC_002',
        priority: 'critical',
        category: 'Reentrancy',
        title: 'Implement Reentrancy Protection',
        description: 'Add nonReentrant modifiers and follow Checks-Effects-Interactions pattern',
        implementationSteps: [
          'Add ReentrancyGuard to all state-modifying functions',
          'Ensure state changes occur before external calls',
          'Add comprehensive testing for reentrancy scenarios'
        ],
        expectedImpact: 'Eliminate reentrancy attack vectors'
      });
    }
    
    const hasAccessControl = vulnerabilities.some(v => v.category === 'access_control');
    if (hasAccessControl) {
      recommendations.push({
        recommendationId: 'REC_003',
        priority: 'high',
        category: 'Access Control',
        title: 'Strengthen Access Control',
        description: 'Add proper authorization checks to privileged functions',
        implementationSteps: [
          'Add onlyOwner/onlyValidator modifiers',
          'Implement role-based access control',
          'Document authorization requirements'
        ],
        expectedImpact: 'Prevent unauthorized access to critical functions'
      });
    }
    
    recommendations.push({
      recommendationId: 'REC_004',
      priority: 'medium',
      category: 'Best Practices',
      title: 'Implement Comprehensive Testing',
      description: 'Add extensive unit and integration tests',
      implementationSteps: [
        'Write tests for all critical paths',
        'Include edge cases and failure scenarios',
        'Achieve >95% code coverage',
        'Add fuzzing tests'
      ],
      expectedImpact: 'Increase confidence in contract correctness'
    });
    
    recommendations.push({
      recommendationId: 'REC_005',
      priority: 'medium',
      category: 'Monitoring',
      title: 'Deploy Runtime Monitoring',
      description: 'Implement runtime invariant checking and alerting',
      implementationSteps: [
        'Add event emissions for critical state changes',
        'Set up monitoring for invariant violations',
        'Implement automated alerts',
        'Create emergency response procedures'
      ],
      expectedImpact: 'Early detection of security incidents'
    });
    
    return recommendations;
  }
  
  private generateProofSummary(
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): ProofSummary {
    let totalProofSteps = 0;
    const proofMethods = {
      symbolicExecution: 0,
      theoremProving: 0,
      modelChecking: 0,
      smtSolver: 0
    };
    let totalVerificationTime = 0;
    
    invariants.checkResults.forEach(result => {
      totalProofSteps += result.proofSteps.length;
      totalVerificationTime += result.verificationTime;
    });
    
    theorems.theorems.forEach(theorem => {
      totalProofSteps += theorem.proof.steps.length;
      
      switch (theorem.proof.proofType) {
        case 'symbolic_execution':
          proofMethods.symbolicExecution++;
          break;
        case 'theorem_proving':
          proofMethods.theoremProving++;
          break;
        case 'model_checking':
          proofMethods.modelChecking++;
          break;
        case 'smt_solver':
          proofMethods.smtSolver++;
          break;
      }
    });
    
    const coverageScore = this.calculateCoverageScore(invariants, theorems);
    
    return {
      totalProofSteps,
      proofMethods,
      verificationTime: totalVerificationTime,
      coverageScore
    };
  }
  
  private calculateCoverageScore(
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): number {
    const invariantScore = (invariants.checkResults.size / Math.max(invariants.invariants.length, 1)) * 50;
    const theoremScore = (theorems.provenTheorems / Math.max(theorems.totalProofs, 1)) * 50;
    
    return Math.round(invariantScore + theoremScore);
  }
  
  private calculateSecurityRating(
    summary: VerificationSummary,
    vulnerabilities: Vulnerability[]
  ): 'SECURE' | 'WARNING' | 'VULNERABLE' | 'CRITICAL' {
    if (summary.criticalIssues > 0) {
      return 'CRITICAL';
    }
    
    if (summary.highIssues > 0 || summary.invariantsViolated > 2) {
      return 'VULNERABLE';
    }
    
    if (summary.mediumIssues > 0 || summary.invariantsViolated > 0) {
      return 'WARNING';
    }
    
    return 'SECURE';
  }
  
  private calculateOverallConfidence(
    invariants: ContractInvariants,
    theorems: SecurityTheorem
  ): number {
    const invariantConfidence = Array.from(invariants.checkResults.values())
      .reduce((sum, r) => sum + r.confidence, 0) / Math.max(invariants.checkResults.size, 1);
    
    const theoremConfidence = theorems.confidence;
    
    return Math.round((invariantConfidence + theoremConfidence) / 2);
  }
  
  private printReportSummary(report: VerificationReport): void {
    console.log(`\n📋 VERIFICATION REPORT: ${report.contractName}`);
    console.log('━'.repeat(80));
    console.log(`Report ID: ${report.reportId}`);
    console.log(`Generated: ${report.generatedAt.toISOString()}`);
    console.log(`Security Rating: ${this.getRatingEmoji(report.securityRating)} ${report.securityRating}`);
    console.log(`Overall Confidence: ${report.overallConfidence}%`);
    console.log('');
    console.log('SUMMARY:');
    console.log(`  Functions Analyzed: ${report.summary.totalFunctions}`);
    console.log(`  Invariants: ${report.summary.invariantsHolding}/${report.summary.totalInvariants} holding`);
    console.log(`  Theorems: ${report.summary.theoremsProven}/${report.summary.totalTheorems} proven`);
    console.log(`  Coverage Score: ${report.proofSummary.coverageScore}%`);
    console.log('');
    console.log('ISSUES:');
    console.log(`  🔴 Critical: ${report.summary.criticalIssues}`);
    console.log(`  🟠 High: ${report.summary.highIssues}`);
    console.log(`  🟡 Medium: ${report.summary.mediumIssues}`);
    console.log(`  🟢 Low: ${report.summary.lowIssues}`);
    console.log('');
    console.log('PROOF METHODS:');
    console.log(`  Symbolic Execution: ${report.proofSummary.proofMethods.symbolicExecution}`);
    console.log(`  Theorem Proving: ${report.proofSummary.proofMethods.theoremProving}`);
    console.log(`  Model Checking: ${report.proofSummary.proofMethods.modelChecking}`);
    console.log(`  SMT Solver: ${report.proofSummary.proofMethods.smtSolver}`);
    console.log('');
    console.log(`RECOMMENDATIONS: ${report.recommendations.length} items`);
    report.recommendations.slice(0, 3).forEach(rec => {
      console.log(`  ${this.getPriorityEmoji(rec.priority)} ${rec.title}`);
    });
    console.log('━'.repeat(80));
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
  
  private getPriorityEmoji(priority: string): string {
    const emojis: Record<string, string> = {
      'critical': '🔴',
      'high': '🟠',
      'medium': '🟡',
      'low': '🟢'
    };
    return emojis[priority] || '⚪';
  }
  
  async exportReport(reportId: string, options: ReportExportOptions): Promise<string> {
    const report = this.reports.get(reportId);
    if (!report) {
      throw new Error(`Report ${reportId} not found`);
    }
    
    switch (options.format) {
      case 'json':
        return this.exportAsJSON(report, options);
      case 'markdown':
        return this.exportAsMarkdown(report, options);
      case 'html':
        return this.exportAsHTML(report, options);
      default:
        return this.exportAsJSON(report, options);
    }
  }
  
  private exportAsJSON(report: VerificationReport, options: ReportExportOptions): string {
    if (options.verbosity === 'minimal') {
      return JSON.stringify({
        reportId: report.reportId,
        contractName: report.contractName,
        securityRating: report.securityRating,
        overallConfidence: report.overallConfidence,
        summary: report.summary
      }, null, 2);
    }
    
    return JSON.stringify(report, null, 2);
  }
  
  private exportAsMarkdown(report: VerificationReport, options: ReportExportOptions): string {
    let markdown = `# Formal Verification Report: ${report.contractName}\n\n`;
    markdown += `**Report ID:** ${report.reportId}\n`;
    markdown += `**Generated:** ${report.generatedAt.toISOString()}\n`;
    markdown += `**Security Rating:** ${report.securityRating}\n`;
    markdown += `**Confidence:** ${report.overallConfidence}%\n\n`;
    
    markdown += `## Summary\n\n`;
    markdown += `- **Functions Analyzed:** ${report.summary.totalFunctions}\n`;
    markdown += `- **Invariants:** ${report.summary.invariantsHolding}/${report.summary.totalInvariants} holding\n`;
    markdown += `- **Theorems:** ${report.summary.theoremsProven}/${report.summary.totalTheorems} proven\n`;
    markdown += `- **Coverage:** ${report.proofSummary.coverageScore}%\n\n`;
    
    if (report.vulnerabilities.length > 0) {
      markdown += `## Vulnerabilities\n\n`;
      report.vulnerabilities.forEach(vuln => {
        markdown += `### ${vuln.title} (${vuln.severity.toUpperCase()})\n\n`;
        markdown += `${vuln.description}\n\n`;
        markdown += `**Recommendation:** ${vuln.recommendation}\n\n`;
      });
    }
    
    markdown += `## Recommendations\n\n`;
    report.recommendations.forEach(rec => {
      markdown += `### ${rec.title} (${rec.priority.toUpperCase()})\n\n`;
      markdown += `${rec.description}\n\n`;
    });
    
    return markdown;
  }
  
  private exportAsHTML(report: VerificationReport, options: ReportExportOptions): string {
    return `
<!DOCTYPE html>
<html>
<head>
  <title>Verification Report: ${report.contractName}</title>
  <style>
    body { font-family: Arial, sans-serif; margin: 40px; }
    .header { background: #f0f0f0; padding: 20px; border-radius: 8px; }
    .rating-SECURE { color: green; }
    .rating-WARNING { color: orange; }
    .rating-VULNERABLE { color: red; }
    .rating-CRITICAL { color: darkred; font-weight: bold; }
  </style>
</head>
<body>
  <div class="header">
    <h1>Formal Verification Report: ${report.contractName}</h1>
    <p><strong>Report ID:</strong> ${report.reportId}</p>
    <p><strong>Security Rating:</strong> <span class="rating-${report.securityRating}">${report.securityRating}</span></p>
    <p><strong>Confidence:</strong> ${report.overallConfidence}%</p>
  </div>
  <h2>Summary</h2>
  <ul>
    <li>Functions: ${report.summary.totalFunctions}</li>
    <li>Invariants: ${report.summary.invariantsHolding}/${report.summary.totalInvariants}</li>
    <li>Theorems: ${report.summary.theoremsProven}/${report.summary.totalTheorems}</li>
  </ul>
</body>
</html>
    `.trim();
  }
  
  getReport(reportId: string): VerificationReport | undefined {
    return this.reports.get(reportId);
  }
  
  getAllReports(): VerificationReport[] {
    return Array.from(this.reports.values());
  }
}
