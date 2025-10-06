import { useQuery } from '@tanstack/react-query';
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Progress } from '@/components/ui/progress';
import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs';
import { LineChart, Line, BarChart, Bar, PieChart, Pie, Cell, XAxis, YAxis, CartesianGrid, Tooltip, Legend, ResponsiveContainer } from 'recharts';
import { Shield, Activity, AlertTriangle, Lock, CheckCircle, XCircle, Clock, TrendingUp, Zap, Database, Eye, FileCheck } from 'lucide-react';
import { useState, useEffect } from 'react';

const COLORS = {
  primary: '#8B5CF6',
  success: '#10B981',
  warning: '#F59E0B',
  danger: '#EF4444',
  info: '#3B82F6'
};

export default function SecurityDashboard() {
  const [selectedSeverity, setSelectedSeverity] = useState<string>('all');

  const { data: overview, isLoading: overviewLoading } = useQuery({
    queryKey: ['/api/security/overview'],
    refetchInterval: 5000
  });

  const { data: chains, isLoading: chainsLoading } = useQuery({
    queryKey: ['/api/security/chains'],
    refetchInterval: 5000
  });

  const { data: threats, isLoading: threatsLoading } = useQuery({
    queryKey: ['/api/security/threats'],
    refetchInterval: 5000
  });

  const { data: quantumMetrics, isLoading: quantumLoading } = useQuery({
    queryKey: ['/api/security/quantum-metrics'],
    refetchInterval: 5000
  });

  const { data: zkProofs, isLoading: zkLoading } = useQuery({
    queryKey: ['/api/security/zk-proofs'],
    refetchInterval: 5000
  });

  const { data: formalVerification, isLoading: verificationLoading } = useQuery({
    queryKey: ['/api/security/formal-verification'],
    refetchInterval: 5000
  });

  const { data: consensus, isLoading: consensusLoading } = useQuery({
    queryKey: ['/api/security/consensus'],
    refetchInterval: 5000
  });

  const getHealthColor = (health: string) => {
    switch (health) {
      case 'excellent': return COLORS.success;
      case 'good': return COLORS.info;
      case 'degraded': return COLORS.warning;
      case 'critical': return COLORS.danger;
      default: return COLORS.info;
    }
  };

  const getSeverityColor = (severity: string) => {
    switch (severity) {
      case 'critical': return 'destructive';
      case 'high': return 'destructive';
      case 'medium': return 'default';
      case 'low': return 'secondary';
      default: return 'outline';
    }
  };

  const filteredThreats = (threats as any[])?.filter((threat: any) => 
    selectedSeverity === 'all' || threat.severity === selectedSeverity
  ) || [];

  const zkProofTypesData = (zkProofs as any)?.proofTypes ? Object.entries((zkProofs as any).proofTypes).map(([name, value]) => ({
    name: name.replace(/([A-Z])/g, ' $1').trim(),
    value
  })) : [];

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-950 via-purple-950 to-slate-950 dark:from-slate-950 dark:via-purple-950 dark:to-slate-950 p-6">
      <div className="max-w-7xl mx-auto space-y-8">
        
        {/* Header */}
        <div className="text-center space-y-4">
          <h1 className="text-4xl md:text-5xl font-bold text-white dark:text-white">
            Trinity Protocol Security Dashboard
          </h1>
          <p className="text-lg text-slate-300 dark:text-slate-400">
            Real-time monitoring across Arbitrum, Solana, and TON networks
          </p>
        </div>

        {/* 1. Overview Panel */}
        <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20" data-testid="overview-panel">
          <CardHeader>
            <CardTitle className="flex items-center gap-2 text-white dark:text-white">
              <Shield className="w-6 h-6 text-purple-400" />
              Security Overview
            </CardTitle>
          </CardHeader>
          <CardContent>
            {overviewLoading ? (
              <div className="text-center py-8 text-slate-400">Loading overview...</div>
            ) : (
              <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6">
                <div className="space-y-2" data-testid="security-score">
                  <p className="text-sm text-slate-400 dark:text-slate-400">Security Score</p>
                  <div className="flex items-center gap-3">
                    <div className="text-4xl font-bold text-white dark:text-white">{(overview as any)?.securityScore}</div>
                    <div className="flex-1">
                      <Progress value={(overview as any)?.securityScore} className="h-2" />
                    </div>
                  </div>
                </div>
                
                <div className="space-y-2" data-testid="active-threats">
                  <p className="text-sm text-slate-400 dark:text-slate-400">Active Threats</p>
                  <div className="flex items-center gap-2">
                    <div className="text-4xl font-bold text-white dark:text-white">{(overview as any)?.activeThreats}</div>
                    {(overview as any)?.activeThreats === 0 && <CheckCircle className="w-6 h-6 text-green-400" />}
                  </div>
                </div>
                
                <div className="space-y-2" data-testid="chains-online">
                  <p className="text-sm text-slate-400 dark:text-slate-400">Chains Online</p>
                  <div className="text-4xl font-bold text-white dark:text-white">
                    {(overview as any)?.chainsOnline}/{(overview as any)?.totalChains}
                  </div>
                </div>
                
                <div className="space-y-2" data-testid="consensus-status">
                  <p className="text-sm text-slate-400 dark:text-slate-400">Consensus Status</p>
                  <Badge className="text-lg px-4 py-1" variant="default">
                    {(overview as any)?.consensusStatus}
                  </Badge>
                  <div className="text-sm text-slate-400 dark:text-slate-400">
                    Rate: {(overview as any)?.consensusRate}%
                  </div>
                </div>
              </div>
            )}
          </CardContent>
        </Card>

        {/* 2. Chain Health Monitoring */}
        <div>
          <h2 className="text-2xl font-bold text-white dark:text-white mb-4 flex items-center gap-2">
            <Activity className="w-6 h-6 text-purple-400" />
            Chain Health Monitoring
          </h2>
          {chainsLoading ? (
            <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20">
              <CardContent className="text-center py-8 text-slate-400">
                Loading chain health...
              </CardContent>
            </Card>
          ) : (
            <div className="grid grid-cols-1 md:grid-cols-3 gap-6">
              {(chains as any[])?.map((chain: any) => (
                <Card 
                  key={chain.id} 
                  className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20"
                  data-testid={`chain-card-${chain.id}`}
                >
                  <CardHeader>
                    <div className="flex items-center justify-between">
                      <CardTitle className="text-white dark:text-white">{chain.name}</CardTitle>
                      <Badge 
                        variant={chain.status === 'online' ? 'default' : 'destructive'}
                        data-testid={`chain-status-${chain.id}`}
                      >
                        {chain.status}
                      </Badge>
                    </div>
                    <CardDescription className="text-slate-400 dark:text-slate-400">
                      Role: {chain.role}
                    </CardDescription>
                  </CardHeader>
                  <CardContent className="space-y-3">
                    <div className="flex justify-between">
                      <span className="text-slate-400 dark:text-slate-400">Block Height:</span>
                      <span className="text-white dark:text-white font-mono">{chain.blockHeight.toLocaleString()}</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-slate-400 dark:text-slate-400">TPS:</span>
                      <span className="text-white dark:text-white font-mono">{chain.tps.toLocaleString()}</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-slate-400 dark:text-slate-400">Latency:</span>
                      <span className="text-white dark:text-white font-mono">{chain.latency}ms</span>
                    </div>
                    <div className="flex justify-between items-center">
                      <span className="text-slate-400 dark:text-slate-400">Health:</span>
                      <Badge style={{ backgroundColor: getHealthColor(chain.health) }}>
                        {chain.health}
                      </Badge>
                    </div>
                  </CardContent>
                </Card>
              ))}
            </div>
          )}
        </div>

        {/* 3. Threat Detection Feed */}
        <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20" data-testid="threat-feed">
          <CardHeader>
            <div className="flex items-center justify-between">
              <CardTitle className="flex items-center gap-2 text-white dark:text-white">
                <AlertTriangle className="w-6 h-6 text-yellow-400" />
                Threat Detection Feed
              </CardTitle>
              <div className="flex gap-2">
                <Badge 
                  variant={selectedSeverity === 'all' ? 'default' : 'outline'}
                  className="cursor-pointer"
                  onClick={() => setSelectedSeverity('all')}
                  data-testid="filter-all"
                >
                  All
                </Badge>
                <Badge 
                  variant={selectedSeverity === 'critical' ? 'destructive' : 'outline'}
                  className="cursor-pointer"
                  onClick={() => setSelectedSeverity('critical')}
                  data-testid="filter-critical"
                >
                  Critical
                </Badge>
                <Badge 
                  variant={selectedSeverity === 'high' ? 'destructive' : 'outline'}
                  className="cursor-pointer"
                  onClick={() => setSelectedSeverity('high')}
                  data-testid="filter-high"
                >
                  High
                </Badge>
              </div>
            </div>
          </CardHeader>
          <CardContent>
            {threatsLoading ? (
              <div className="text-center py-8 text-slate-400">Loading threats...</div>
            ) : (
              <div className="space-y-3 max-h-96 overflow-y-auto">
                {filteredThreats.map((threat: any) => (
                  <div 
                    key={threat.id} 
                    className="flex items-center justify-between p-4 bg-slate-800/50 rounded-lg border border-slate-700"
                    data-testid={`threat-${threat.id}`}
                  >
                    <div className="flex-1 space-y-1">
                      <div className="flex items-center gap-2">
                        <Badge variant={getSeverityColor(threat.severity) as any}>
                          {threat.severity}
                        </Badge>
                        <span className="text-sm text-slate-400 dark:text-slate-400">
                          {new Date(threat.timestamp).toLocaleString()}
                        </span>
                      </div>
                      <p className="text-white dark:text-white">{threat.description}</p>
                      <p className="text-sm text-slate-400 dark:text-slate-400">Source: {threat.source}</p>
                    </div>
                    <div className="flex items-center gap-2">
                      <Badge variant={threat.blocked ? 'default' : 'secondary'}>
                        {threat.status}
                      </Badge>
                      {threat.blocked && <Shield className="w-5 h-5 text-green-400" />}
                    </div>
                  </div>
                ))}
              </div>
            )}
          </CardContent>
        </Card>

        <Tabs defaultValue="quantum" className="space-y-4">
          <TabsList className="grid w-full grid-cols-4 bg-slate-900/50 dark:bg-slate-900/50">
            <TabsTrigger value="quantum" data-testid="tab-quantum">Quantum Crypto</TabsTrigger>
            <TabsTrigger value="zk" data-testid="tab-zk">ZK Proofs</TabsTrigger>
            <TabsTrigger value="verification" data-testid="tab-verification">Formal Verification</TabsTrigger>
            <TabsTrigger value="consensus" data-testid="tab-consensus">Consensus</TabsTrigger>
          </TabsList>

          {/* 4. Quantum Crypto Metrics */}
          <TabsContent value="quantum" data-testid="quantum-metrics-panel">
            <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20">
              <CardHeader>
                <CardTitle className="flex items-center gap-2 text-white dark:text-white">
                  <Lock className="w-6 h-6 text-purple-400" />
                  Quantum-Resistant Cryptography
                </CardTitle>
              </CardHeader>
              <CardContent>
                {quantumLoading ? (
                  <div className="text-center py-8 text-slate-400">Loading quantum metrics...</div>
                ) : (
                  <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6">
                    <Card className="bg-slate-800/50 border-slate-700" data-testid="key-generation">
                      <CardHeader className="pb-3">
                        <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Key Generation</CardTitle>
                      </CardHeader>
                      <CardContent>
                        <div className="text-3xl font-bold text-white dark:text-white mb-2">
                          {(quantumMetrics as any)?.keyGeneration?.speed}
                        </div>
                        <p className="text-sm text-slate-400 dark:text-slate-400">keys/sec</p>
                        <p className="text-xs text-slate-500 dark:text-slate-500 mt-2">{(quantumMetrics as any)?.keyGeneration?.algorithm}</p>
                      </CardContent>
                    </Card>

                    <Card className="bg-slate-800/50 border-slate-700" data-testid="signature-verification">
                      <CardHeader className="pb-3">
                        <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Signature Verification</CardTitle>
                      </CardHeader>
                      <CardContent>
                        <div className="text-3xl font-bold text-white dark:text-white mb-2">
                          {(quantumMetrics as any)?.signatureVerification?.speed}
                        </div>
                        <p className="text-sm text-slate-400 dark:text-slate-400">ops/sec</p>
                        <p className="text-xs text-slate-500 dark:text-slate-500 mt-2">{(quantumMetrics as any)?.signatureVerification?.algorithm}</p>
                      </CardContent>
                    </Card>

                    <Card className="bg-slate-800/50 border-slate-700" data-testid="encryption-throughput">
                      <CardHeader className="pb-3">
                        <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Encryption</CardTitle>
                      </CardHeader>
                      <CardContent>
                        <div className="text-3xl font-bold text-white dark:text-white mb-2">
                          {(quantumMetrics as any)?.encryption?.throughput}
                        </div>
                        <p className="text-sm text-slate-400 dark:text-slate-400">MB/sec</p>
                        <p className="text-xs text-slate-500 dark:text-slate-500 mt-2">Avg: {(quantumMetrics as any)?.encryption?.avgTime}ms</p>
                      </CardContent>
                    </Card>

                    <Card className="bg-slate-800/50 border-slate-700" data-testid="decryption-throughput">
                      <CardHeader className="pb-3">
                        <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Decryption</CardTitle>
                      </CardHeader>
                      <CardContent>
                        <div className="text-3xl font-bold text-white dark:text-white mb-2">
                          {(quantumMetrics as any)?.decryption?.throughput}
                        </div>
                        <p className="text-sm text-slate-400 dark:text-slate-400">MB/sec</p>
                        <p className="text-xs text-slate-500 dark:text-slate-500 mt-2">Avg: {(quantumMetrics as any)?.decryption?.avgTime}ms</p>
                      </CardContent>
                    </Card>
                  </div>
                )}
              </CardContent>
            </Card>
          </TabsContent>

          {/* 5. ZK Proof Statistics */}
          <TabsContent value="zk" data-testid="zk-proofs-panel">
            <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20">
              <CardHeader>
                <CardTitle className="flex items-center gap-2 text-white dark:text-white">
                  <Eye className="w-6 h-6 text-purple-400" />
                  Zero-Knowledge Proof System
                </CardTitle>
              </CardHeader>
              <CardContent>
                {zkLoading ? (
                  <div className="text-center py-8 text-slate-400">Loading ZK proof stats...</div>
                ) : (
                  <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
                    <div className="space-y-4">
                      <div className="grid grid-cols-2 gap-4">
                        <Card className="bg-slate-800/50 border-slate-700" data-testid="total-proofs">
                          <CardHeader className="pb-3">
                            <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Total Proofs</CardTitle>
                          </CardHeader>
                          <CardContent>
                            <div className="text-3xl font-bold text-white dark:text-white">
                              {(zkProofs as any)?.totalProofs?.toLocaleString()}
                            </div>
                          </CardContent>
                        </Card>

                        <Card className="bg-slate-800/50 border-slate-700" data-testid="proofs-today">
                          <CardHeader className="pb-3">
                            <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Today</CardTitle>
                          </CardHeader>
                          <CardContent>
                            <div className="text-3xl font-bold text-white dark:text-white">
                              {(zkProofs as any)?.proofsToday?.toLocaleString()}
                            </div>
                          </CardContent>
                        </Card>

                        <Card className="bg-slate-800/50 border-slate-700" data-testid="avg-generation-time">
                          <CardHeader className="pb-3">
                            <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Avg Generation</CardTitle>
                          </CardHeader>
                          <CardContent>
                            <div className="text-3xl font-bold text-white dark:text-white">
                              {(zkProofs as any)?.averageGenerationTime}
                            </div>
                            <p className="text-sm text-slate-400 dark:text-slate-400">ms</p>
                          </CardContent>
                        </Card>

                        <Card className="bg-slate-800/50 border-slate-700" data-testid="verification-success-rate">
                          <CardHeader className="pb-3">
                            <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Success Rate</CardTitle>
                          </CardHeader>
                          <CardContent>
                            <div className="text-3xl font-bold text-white dark:text-white">
                              {(zkProofs as any)?.verificationSuccessRate}%
                            </div>
                          </CardContent>
                        </Card>
                      </div>
                    </div>

                    <div>
                      <h3 className="text-sm font-medium text-slate-400 dark:text-slate-400 mb-4">Proof Types Distribution</h3>
                      <ResponsiveContainer width="100%" height={250}>
                        <PieChart>
                          <Pie
                            data={zkProofTypesData}
                            cx="50%"
                            cy="50%"
                            labelLine={false}
                            label={({ name, percent }) => `${name}: ${(percent * 100).toFixed(0)}%`}
                            outerRadius={80}
                            fill="#8884d8"
                            dataKey="value"
                          >
                            {zkProofTypesData.map((entry: any, index: number) => (
                              <Cell key={`cell-${index}`} fill={Object.values(COLORS)[index % Object.values(COLORS).length]} />
                            ))}
                          </Pie>
                          <Tooltip />
                        </PieChart>
                      </ResponsiveContainer>
                    </div>
                  </div>
                )}
              </CardContent>
            </Card>
          </TabsContent>

          {/* 6. Formal Verification Results */}
          <TabsContent value="verification" data-testid="verification-panel">
            <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20">
              <CardHeader>
                <CardTitle className="flex items-center gap-2 text-white dark:text-white">
                  <FileCheck className="w-6 h-6 text-purple-400" />
                  Formal Verification Results
                </CardTitle>
              </CardHeader>
              <CardContent>
                {verificationLoading ? (
                  <div className="text-center py-8 text-slate-400">Loading verification results...</div>
                ) : (
                  <div className="space-y-6">
                    <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
                      <Card className="bg-slate-800/50 border-slate-700" data-testid="theorems-proven">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Theorems Proven</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-3xl font-bold text-white dark:text-white">
                            {(formalVerification as any)?.summary?.totalTheoremsProven}/{(formalVerification as any)?.summary?.totalTheorems}
                          </div>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="invariants-holding">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Invariants Holding</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-3xl font-bold text-white dark:text-white">
                            {(formalVerification as any)?.summary?.totalInvariantsHolding}/{(formalVerification as any)?.summary?.totalInvariants}
                          </div>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="confidence-score">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Confidence Score</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-3xl font-bold text-white dark:text-white">
                            {(formalVerification as any)?.summary?.overallConfidence}%
                          </div>
                        </CardContent>
                      </Card>
                    </div>

                    <div className="space-y-3">
                      {(formalVerification as any)?.contracts?.map((contract: any) => (
                        <Card key={contract.name} className="bg-slate-800/50 border-slate-700" data-testid={`contract-${contract.name}`}>
                          <CardHeader>
                            <div className="flex items-center justify-between">
                              <CardTitle className="text-white dark:text-white">{contract.name}</CardTitle>
                              <Badge variant={contract.verified ? 'default' : 'destructive'}>
                                {contract.verified ? 'Verified' : 'Unverified'}
                              </Badge>
                            </div>
                          </CardHeader>
                          <CardContent>
                            <div className="grid grid-cols-2 md:grid-cols-4 gap-4 text-sm">
                              <div>
                                <p className="text-slate-400 dark:text-slate-400">Theorems</p>
                                <p className="text-white dark:text-white font-mono">{contract.theoremsProven}/{contract.totalTheorems}</p>
                              </div>
                              <div>
                                <p className="text-slate-400 dark:text-slate-400">Invariants</p>
                                <p className="text-white dark:text-white font-mono">{contract.invariantsHolding}/{contract.totalInvariants}</p>
                              </div>
                              <div>
                                <p className="text-slate-400 dark:text-slate-400">Vulnerabilities</p>
                                <p className="text-white dark:text-white font-mono">{contract.criticalVulnerabilities}</p>
                              </div>
                              <div>
                                <p className="text-slate-400 dark:text-slate-400">Confidence</p>
                                <p className="text-white dark:text-white font-mono">{contract.confidenceScore}%</p>
                              </div>
                            </div>
                          </CardContent>
                        </Card>
                      ))}
                    </div>
                  </div>
                )}
              </CardContent>
            </Card>
          </TabsContent>

          {/* 7. Consensus Monitoring */}
          <TabsContent value="consensus" data-testid="consensus-panel">
            <Card className="bg-slate-900/50 border-purple-500/20 dark:bg-slate-900/50 dark:border-purple-500/20">
              <CardHeader>
                <CardTitle className="flex items-center gap-2 text-white dark:text-white">
                  <Database className="w-6 h-6 text-purple-400" />
                  Trinity Protocol Consensus
                </CardTitle>
              </CardHeader>
              <CardContent>
                {consensusLoading ? (
                  <div className="text-center py-8 text-slate-400">Loading consensus data...</div>
                ) : (
                  <div className="space-y-6">
                    <div className="grid grid-cols-1 md:grid-cols-4 gap-4">
                      <Card className="bg-slate-800/50 border-slate-700" data-testid="consensus-rate">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Consensus Rate</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-3xl font-bold text-white dark:text-white">
                            {(consensus as any)?.consensusRate}%
                          </div>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="avg-consensus-time">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Avg Time</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-3xl font-bold text-white dark:text-white">
                            {(consensus as any)?.averageConsensusTime}
                          </div>
                          <p className="text-sm text-slate-400 dark:text-slate-400">ms</p>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="byzantine-tolerance">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Byzantine Tolerance</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <Badge variant="default" className="text-lg">
                            {(consensus as any)?.byzantineTolerance}
                          </Badge>
                          <p className="text-sm text-slate-400 dark:text-slate-400 mt-2">
                            Faults: {(consensus as any)?.currentByzantineFaults}/{(consensus as any)?.maxByzantineFaults}
                          </p>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="attack-probability">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Attack Probability</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="text-2xl font-bold text-white dark:text-white">
                            {(consensus as any)?.attackProbability}
                          </div>
                        </CardContent>
                      </Card>
                    </div>

                    <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                      <Card className="bg-slate-800/50 border-slate-700" data-testid="safety-proof">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Safety Proof</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="flex items-center gap-2">
                            {(consensus as any)?.safetyProof?.verified ? (
                              <CheckCircle className="w-6 h-6 text-green-400" />
                            ) : (
                              <XCircle className="w-6 h-6 text-red-400" />
                            )}
                            <span className="text-white dark:text-white">
                              {(consensus as any)?.safetyProof?.verified ? 'Verified' : 'Failed'}
                            </span>
                            <Badge variant="outline" className="ml-auto">
                              {(consensus as any)?.safetyProof?.confidence}% confidence
                            </Badge>
                          </div>
                        </CardContent>
                      </Card>

                      <Card className="bg-slate-800/50 border-slate-700" data-testid="liveness-proof">
                        <CardHeader className="pb-3">
                          <CardTitle className="text-sm text-slate-400 dark:text-slate-400">Liveness Proof</CardTitle>
                        </CardHeader>
                        <CardContent>
                          <div className="flex items-center gap-2">
                            {(consensus as any)?.livenessProof?.verified ? (
                              <CheckCircle className="w-6 h-6 text-green-400" />
                            ) : (
                              <XCircle className="w-6 h-6 text-red-400" />
                            )}
                            <span className="text-white dark:text-white">
                              {(consensus as any)?.livenessProof?.verified ? 'Verified' : 'Failed'}
                            </span>
                            <Badge variant="outline" className="ml-auto">
                              {(consensus as any)?.livenessProof?.confidence}% confidence
                            </Badge>
                          </div>
                        </CardContent>
                      </Card>
                    </div>

                    <div>
                      <h3 className="text-sm font-medium text-slate-400 dark:text-slate-400 mb-4">Consensus Rate (Last 24h)</h3>
                      <ResponsiveContainer width="100%" height={200}>
                        <LineChart data={(consensus as any)?.consensusHistory || []}>
                          <CartesianGrid strokeDasharray="3 3" stroke="#334155" />
                          <XAxis 
                            dataKey="timestamp" 
                            stroke="#94a3b8"
                            tickFormatter={(timestamp) => new Date(timestamp).toLocaleTimeString([], { hour: '2-digit' })}
                          />
                          <YAxis stroke="#94a3b8" />
                          <Tooltip 
                            contentStyle={{ backgroundColor: '#1e293b', border: '1px solid #475569' }}
                            labelStyle={{ color: '#e2e8f0' }}
                          />
                          <Line type="monotone" dataKey="rate" stroke={COLORS.primary} strokeWidth={2} />
                        </LineChart>
                      </ResponsiveContainer>
                    </div>
                  </div>
                )}
              </CardContent>
            </Card>
          </TabsContent>
        </Tabs>
      </div>
    </div>
  );
}
