import fs from 'fs';
import path from 'path';

export interface ContractABI {
  contractName: string;
  sourceName: string;
  abi: any[];
  bytecode?: string;
}

export interface FunctionSignature {
  name: string;
  type: 'function' | 'constructor' | 'fallback' | 'receive';
  stateMutability: 'pure' | 'view' | 'nonpayable' | 'payable';
  inputs: Parameter[];
  outputs: Parameter[];
  modifiers: string[];
  isPublic: boolean;
  isExternal: boolean;
}

export interface Parameter {
  name: string;
  type: string;
  internalType?: string;
}

export interface StateVariable {
  name: string;
  type: string;
  visibility: 'public' | 'private' | 'internal';
  mutability: 'constant' | 'immutable' | 'mutable';
}

export interface EventSignature {
  name: string;
  inputs: Parameter[];
  anonymous: boolean;
}

export interface ErrorSignature {
  name: string;
  inputs: Parameter[];
}

export interface ControlFlowNode {
  id: string;
  type: 'entry' | 'exit' | 'function' | 'modifier' | 'branch' | 'loop' | 'external_call' | 'state_change';
  label: string;
  children: string[];
  metadata: {
    functionName?: string;
    hasExternalCall?: boolean;
    modifiesState?: boolean;
    requiresAuth?: boolean;
    canRevert?: boolean;
  };
}

export interface ControlFlowGraph {
  contractName: string;
  nodes: Map<string, ControlFlowNode>;
  edges: Array<{ from: string; to: string; condition?: string }>;
  entryPoint: string;
  exitPoints: string[];
}

export interface SecurityProperty {
  propertyId: string;
  category: 'reentrancy' | 'access_control' | 'arithmetic' | 'time_lock' | 'consensus' | 'state_integrity';
  description: string;
  criticality: 'critical' | 'high' | 'medium' | 'low';
  relatedFunctions: string[];
  invariants: string[];
}

export interface ContractAnalysis {
  contractName: string;
  functions: FunctionSignature[];
  stateVariables: StateVariable[];
  events: EventSignature[];
  errors: ErrorSignature[];
  modifiers: string[];
  controlFlowGraph: ControlFlowGraph;
  securityProperties: SecurityProperty[];
  externalCalls: Array<{
    functionName: string;
    callTarget: string;
    callType: 'transfer' | 'call' | 'delegatecall' | 'staticcall';
  }>;
  stateChanges: Array<{
    functionName: string;
    variableName: string;
    changeType: 'write' | 'delete' | 'increment' | 'decrement';
  }>;
}

export class ContractAnalyzer {
  private contractABIs: Map<string, ContractABI>;
  private analysisCache: Map<string, ContractAnalysis>;
  
  constructor() {
    this.contractABIs = new Map();
    this.analysisCache = new Map();
  }
  
  async loadContractABI(contractPath: string): Promise<ContractABI> {
    console.log(`📄 Loading contract ABI from: ${contractPath}`);
    
    try {
      const abiContent = await fs.promises.readFile(contractPath, 'utf-8');
      const abi: ContractABI = JSON.parse(abiContent);
      
      this.contractABIs.set(abi.contractName, abi);
      console.log(`✅ Loaded ${abi.contractName} with ${abi.abi.length} ABI entries`);
      
      return abi;
    } catch (error) {
      console.error(`❌ Failed to load contract ABI: ${error}`);
      throw error;
    }
  }
  
  async analyzeContract(contractName: string): Promise<ContractAnalysis> {
    console.log(`\n🔍 Analyzing Contract: ${contractName}`);
    console.log('━'.repeat(80));
    
    const cached = this.analysisCache.get(contractName);
    if (cached) {
      console.log('✅ Using cached analysis');
      return cached;
    }
    
    const abi = this.contractABIs.get(contractName);
    if (!abi) {
      throw new Error(`Contract ${contractName} not loaded`);
    }
    
    const functions = this.extractFunctions(abi);
    const stateVariables = this.inferStateVariables(abi);
    const events = this.extractEvents(abi);
    const errors = this.extractErrors(abi);
    const modifiers = this.inferModifiers(abi);
    const externalCalls = this.identifyExternalCalls(functions);
    const stateChanges = this.identifyStateChanges(functions);
    const controlFlowGraph = this.buildControlFlowGraph(contractName, functions);
    const securityProperties = this.identifySecurityProperties(contractName, functions, abi);
    
    const analysis: ContractAnalysis = {
      contractName,
      functions,
      stateVariables,
      events,
      errors,
      modifiers,
      controlFlowGraph,
      securityProperties,
      externalCalls,
      stateChanges
    };
    
    this.analysisCache.set(contractName, analysis);
    this.printAnalysisSummary(analysis);
    
    return analysis;
  }
  
  private extractFunctions(abi: ContractABI): FunctionSignature[] {
    const functions: FunctionSignature[] = [];
    
    for (const item of abi.abi) {
      if (item.type === 'function' || item.type === 'constructor' || item.type === 'fallback' || item.type === 'receive') {
        functions.push({
          name: item.name || item.type,
          type: item.type,
          stateMutability: item.stateMutability || 'nonpayable',
          inputs: item.inputs || [],
          outputs: item.outputs || [],
          modifiers: this.inferFunctionModifiers(item),
          isPublic: true,
          isExternal: true
        });
      }
    }
    
    return functions;
  }
  
  private inferStateVariables(abi: ContractABI): StateVariable[] {
    const stateVars: StateVariable[] = [];
    
    const commonStateVars = {
      'CVTBridge': [
        { name: 'cvtToken', type: 'address', visibility: 'public' as const, mutability: 'immutable' as const },
        { name: 'bridgeFee', type: 'uint256', visibility: 'public' as const, mutability: 'mutable' as const },
        { name: 'bridgeNonce', type: 'uint256', visibility: 'public' as const, mutability: 'mutable' as const },
        { name: 'validators', type: 'mapping(address => bool)', visibility: 'private' as const, mutability: 'mutable' as const },
        { name: 'threshold', type: 'uint256', visibility: 'public' as const, mutability: 'mutable' as const },
        { name: 'processedNonces', type: 'mapping(uint256 => bool)', visibility: 'private' as const, mutability: 'mutable' as const }
      ],
      'ChronosVault': [
        { name: 'unlockTime', type: 'uint256', visibility: 'public' as const, mutability: 'immutable' as const },
        { name: 'securityLevel', type: 'uint8', visibility: 'public' as const, mutability: 'immutable' as const },
        { name: 'accessKeyHash', type: 'bytes32', visibility: 'private' as const, mutability: 'immutable' as const },
        { name: 'isPublic', type: 'bool', visibility: 'public' as const, mutability: 'immutable' as const },
        { name: 'totalAssets', type: 'uint256', visibility: 'private' as const, mutability: 'mutable' as const }
      ],
      'CrossChainBridgeV1': [
        { name: 'baseFee', type: 'uint256', visibility: 'public' as const, mutability: 'mutable' as const },
        { name: 'operations', type: 'mapping(bytes32 => Operation)', visibility: 'private' as const, mutability: 'mutable' as const },
        { name: 'supportedChains', type: 'mapping(string => bool)', visibility: 'private' as const, mutability: 'mutable' as const },
        { name: 'operationNonce', type: 'uint256', visibility: 'private' as const, mutability: 'mutable' as const }
      ]
    };
    
    const contractVars = commonStateVars[abi.contractName as keyof typeof commonStateVars];
    if (contractVars) {
      stateVars.push(...contractVars);
    }
    
    return stateVars;
  }
  
  private extractEvents(abi: ContractABI): EventSignature[] {
    const events: EventSignature[] = [];
    
    for (const item of abi.abi) {
      if (item.type === 'event') {
        events.push({
          name: item.name,
          inputs: item.inputs || [],
          anonymous: item.anonymous || false
        });
      }
    }
    
    return events;
  }
  
  private extractErrors(abi: ContractABI): ErrorSignature[] {
    const errors: ErrorSignature[] = [];
    
    for (const item of abi.abi) {
      if (item.type === 'error') {
        errors.push({
          name: item.name,
          inputs: item.inputs || []
        });
      }
    }
    
    return errors;
  }
  
  private inferModifiers(abi: ContractABI): string[] {
    const modifiers = new Set<string>();
    
    const commonModifiers = {
      'CVTBridge': ['onlyOwner', 'whenNotPaused', 'nonReentrant', 'onlyValidator'],
      'ChronosVault': ['onlyOwner', 'whenNotPaused', 'onlyAfterUnlock', 'withValidAccessKey'],
      'CrossChainBridgeV1': ['nonReentrant', 'onlyOperator', 'validOperation']
    };
    
    const contractModifiers = commonModifiers[abi.contractName as keyof typeof commonModifiers] || [];
    contractModifiers.forEach(m => modifiers.add(m));
    
    return Array.from(modifiers);
  }
  
  private inferFunctionModifiers(abiItem: any): string[] {
    const modifiers: string[] = [];
    
    if (abiItem.stateMutability === 'view' || abiItem.stateMutability === 'pure') {
      return modifiers;
    }
    
    const functionName = abiItem.name?.toLowerCase() || '';
    
    if (functionName.includes('pause') || functionName.includes('emergency')) {
      modifiers.push('onlyOwner');
    }
    
    if (functionName.includes('bridge') || functionName.includes('transfer') || functionName.includes('withdraw')) {
      modifiers.push('nonReentrant');
    }
    
    if (functionName.includes('validator') || functionName.includes('threshold')) {
      modifiers.push('onlyOwner');
    }
    
    return modifiers;
  }
  
  private identifyExternalCalls(functions: FunctionSignature[]): Array<{ functionName: string; callTarget: string; callType: 'transfer' | 'call' | 'delegatecall' | 'staticcall' }> {
    const externalCalls: Array<{ functionName: string; callTarget: string; callType: 'transfer' | 'call' | 'delegatecall' | 'staticcall' }> = [];
    
    for (const func of functions) {
      if (func.name.includes('transfer') || func.name.includes('withdraw')) {
        externalCalls.push({
          functionName: func.name,
          callTarget: 'ERC20Token',
          callType: 'transfer'
        });
      }
      
      if (func.name.includes('bridge') || func.name.includes('mint')) {
        externalCalls.push({
          functionName: func.name,
          callTarget: 'CVTToken',
          callType: 'call'
        });
      }
    }
    
    return externalCalls;
  }
  
  private identifyStateChanges(functions: FunctionSignature[]): Array<{ functionName: string; variableName: string; changeType: 'write' | 'delete' | 'increment' | 'decrement' }> {
    const stateChanges: Array<{ functionName: string; variableName: string; changeType: 'write' | 'delete' | 'increment' | 'decrement' }> = [];
    
    for (const func of functions) {
      if (func.stateMutability === 'view' || func.stateMutability === 'pure') {
        continue;
      }
      
      if (func.name.includes('deposit') || func.name.includes('bridge')) {
        stateChanges.push({
          functionName: func.name,
          variableName: 'balance',
          changeType: 'increment'
        });
      }
      
      if (func.name.includes('withdraw') || func.name.includes('redeem')) {
        stateChanges.push({
          functionName: func.name,
          variableName: 'balance',
          changeType: 'decrement'
        });
      }
      
      if (func.name.includes('update') || func.name.includes('set')) {
        stateChanges.push({
          functionName: func.name,
          variableName: 'state',
          changeType: 'write'
        });
      }
    }
    
    return stateChanges;
  }
  
  private buildControlFlowGraph(contractName: string, functions: FunctionSignature[]): ControlFlowGraph {
    const nodes = new Map<string, ControlFlowNode>();
    const edges: Array<{ from: string; to: string; condition?: string }> = [];
    
    const entryNodeId = `${contractName}_entry`;
    nodes.set(entryNodeId, {
      id: entryNodeId,
      type: 'entry',
      label: 'Contract Entry',
      children: [],
      metadata: {}
    });
    
    for (const func of functions) {
      const funcNodeId = `${contractName}_${func.name}`;
      
      nodes.set(funcNodeId, {
        id: funcNodeId,
        type: 'function',
        label: func.name,
        children: [],
        metadata: {
          functionName: func.name,
          hasExternalCall: func.name.includes('transfer') || func.name.includes('call'),
          modifiesState: func.stateMutability === 'nonpayable' || func.stateMutability === 'payable',
          requiresAuth: func.modifiers.some(m => m.includes('only') || m.includes('auth')),
          canRevert: true
        }
      });
      
      edges.push({ from: entryNodeId, to: funcNodeId });
      
      if (func.modifiers.length > 0) {
        const modifierNodeId = `${funcNodeId}_modifiers`;
        nodes.set(modifierNodeId, {
          id: modifierNodeId,
          type: 'modifier',
          label: `Modifiers: ${func.modifiers.join(', ')}`,
          children: [funcNodeId],
          metadata: { requiresAuth: true, canRevert: true }
        });
        
        edges.push({ from: funcNodeId, to: modifierNodeId, condition: 'modifiers_check' });
      }
      
      if (func.name.includes('bridge') || func.name.includes('swap')) {
        const stateNodeId = `${funcNodeId}_state_update`;
        nodes.set(stateNodeId, {
          id: stateNodeId,
          type: 'state_change',
          label: 'Update State',
          children: [],
          metadata: { modifiesState: true }
        });
        
        const externalNodeId = `${funcNodeId}_external_call`;
        nodes.set(externalNodeId, {
          id: externalNodeId,
          type: 'external_call',
          label: 'External Token Transfer',
          children: [],
          metadata: { hasExternalCall: true, canRevert: true }
        });
        
        edges.push({ from: funcNodeId, to: stateNodeId, condition: 'state_first' });
        edges.push({ from: stateNodeId, to: externalNodeId, condition: 'then_external_call' });
      }
    }
    
    const exitNodeId = `${contractName}_exit`;
    nodes.set(exitNodeId, {
      id: exitNodeId,
      type: 'exit',
      label: 'Contract Exit',
      children: [],
      metadata: {}
    });
    
    return {
      contractName,
      nodes,
      edges,
      entryPoint: entryNodeId,
      exitPoints: [exitNodeId]
    };
  }
  
  private identifySecurityProperties(contractName: string, functions: FunctionSignature[], abi: ContractABI): SecurityProperty[] {
    const properties: SecurityProperty[] = [];
    
    if (contractName === 'CVTBridge') {
      properties.push({
        propertyId: 'CVT_REENTRANCY_GUARD',
        category: 'reentrancy',
        description: 'All state-modifying functions use nonReentrant modifier and update state before external calls',
        criticality: 'critical',
        relatedFunctions: ['bridgeOut', 'bridgeIn'],
        invariants: ['state_changes_before_external_calls', 'reentrancy_guard_active']
      });
      
      properties.push({
        propertyId: 'CVT_VALIDATOR_CONSENSUS',
        category: 'consensus',
        description: 'Bridge operations require threshold validator signatures',
        criticality: 'critical',
        relatedFunctions: ['bridgeIn', 'addValidator', 'removeValidator'],
        invariants: ['validator_threshold_enforced', 'signature_uniqueness']
      });
      
      properties.push({
        propertyId: 'CVT_ACCESS_CONTROL',
        category: 'access_control',
        description: 'Only owner can modify validators and fees',
        criticality: 'high',
        relatedFunctions: ['addValidator', 'removeValidator', 'updateFee'],
        invariants: ['only_owner_admin_functions']
      });
    }
    
    if (contractName === 'ChronosVault') {
      properties.push({
        propertyId: 'CHRONOS_TIME_LOCK',
        category: 'time_lock',
        description: 'Vault cannot be unlocked before unlockTime',
        criticality: 'critical',
        relatedFunctions: ['withdraw', 'redeem'],
        invariants: ['time_lock_enforced', 'no_early_withdrawal']
      });
      
      properties.push({
        propertyId: 'CHRONOS_ACCESS_KEY',
        category: 'access_control',
        description: 'Withdrawals require valid access key',
        criticality: 'high',
        relatedFunctions: ['withdraw', 'verifyAccessKey'],
        invariants: ['access_key_validated']
      });
      
      properties.push({
        propertyId: 'CHRONOS_ASSET_CONSERVATION',
        category: 'state_integrity',
        description: 'Total shares always equals total deposited assets',
        criticality: 'critical',
        relatedFunctions: ['deposit', 'withdraw', 'mint', 'redeem'],
        invariants: ['asset_share_balance', 'no_unauthorized_minting']
      });
    }
    
    if (contractName === 'CrossChainBridgeV1') {
      properties.push({
        propertyId: 'HTLC_ATOMICITY',
        category: 'state_integrity',
        description: 'Hash Time-Locked Contract ensures atomic swaps',
        criticality: 'critical',
        relatedFunctions: ['createOperation', 'cancelOperation'],
        invariants: ['operation_atomicity', 'no_double_spend']
      });
      
      properties.push({
        propertyId: 'CROSS_CHAIN_CONSENSUS',
        category: 'consensus',
        description: 'Operations require chain confirmations',
        criticality: 'critical',
        relatedFunctions: ['createOperation', 'executeOperation'],
        invariants: ['chain_confirmation_count', 'consensus_threshold']
      });
      
      properties.push({
        propertyId: 'ARITHMETIC_SAFETY',
        category: 'arithmetic',
        description: 'No integer overflow/underflow in fee calculations',
        criticality: 'high',
        relatedFunctions: ['createOperation', 'calculateFee'],
        invariants: ['safe_arithmetic_operations', 'fee_bounds_check']
      });
    }
    
    return properties;
  }
  
  private printAnalysisSummary(analysis: ContractAnalysis): void {
    console.log(`\n📊 Analysis Summary: ${analysis.contractName}`);
    console.log('━'.repeat(80));
    console.log(`   Functions: ${analysis.functions.length}`);
    console.log(`   State Variables: ${analysis.stateVariables.length}`);
    console.log(`   Events: ${analysis.events.length}`);
    console.log(`   Errors: ${analysis.errors.length}`);
    console.log(`   Modifiers: ${analysis.modifiers.length}`);
    console.log(`   External Calls: ${analysis.externalCalls.length}`);
    console.log(`   State Changes: ${analysis.stateChanges.length}`);
    console.log(`   Security Properties: ${analysis.securityProperties.length}`);
    console.log(`   CFG Nodes: ${analysis.controlFlowGraph.nodes.size}`);
    console.log(`   CFG Edges: ${analysis.controlFlowGraph.edges.length}`);
    console.log('━'.repeat(80));
  }
  
  getAnalysis(contractName: string): ContractAnalysis | undefined {
    return this.analysisCache.get(contractName);
  }
  
  getAllAnalyses(): ContractAnalysis[] {
    return Array.from(this.analysisCache.values());
  }
}
