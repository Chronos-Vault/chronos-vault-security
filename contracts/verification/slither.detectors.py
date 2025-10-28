"""
Custom Slither Detectors for Trinity Protocol
Chronos Vault - Advanced Security Analysis

These custom detectors check for Trinity Protocol-specific vulnerabilities
that standard Slither detectors miss.
"""

from slither.detectors.abstract_detector import AbstractDetector, DetectorClassification


class TrinityConsensusDetector(AbstractDetector):
    """
    Detects violations of Trinity Protocol's 2-of-3 consensus requirement
    """
    
    ARGUMENT = 'trinity-consensus'
    HELP = 'Trinity Protocol consensus violations'
    IMPACT = DetectorClassification.HIGH
    CONFIDENCE = DetectorClassification.HIGH

    WIKI = 'https://github.com/Chronos-Vault/trinity-protocol/wiki/Consensus'
    WIKI_TITLE = 'Trinity Protocol 2-of-3 Consensus'
    WIKI_DESCRIPTION = 'Operations must require exactly 2-of-3 chain approvals'
    WIKI_EXPLOIT_SCENARIO = 'If threshold < 2, single chain can approve operations'
    WIKI_RECOMMENDATION = 'Ensure requiredChainConfirmations == 2 and immutable'

    def _detect(self):
        results = []
        
        for contract in self.compilation_unit.contracts_derived:
            # Check for Trinity Protocol contracts
            if 'CrossChain' in contract.name or 'Bridge' in contract.name:
                # Find requiredChainConfirmations variable
                for var in contract.state_variables:
                    if 'requiredChainConfirmations' in var.name or 'REQUIRED_CHAIN_CONFIRMATIONS' in var.name:
                        # Check if it's immutable
                        if not var.is_immutable and not var.is_constant:
                            info = [
                                'Trinity Protocol consensus variable ',
                                var,
                                ' should be immutable to prevent modification\n'
                            ]
                            res = self.generate_result(info)
                            results.append(res)
                        
                        # Check if it's set to 2
                        if var.expression:
                            if str(var.expression) != '2':
                                info = [
                                    'Trinity Protocol consensus threshold ',
                                    var,
                                    ' must be exactly 2 (2-of-3 consensus)\n'
                                ]
                                res = self.generate_result(info)
                                results.append(res)
        
        return results


class ChainIdBindingDetector(AbstractDetector):
    """
    Detects missing ChainId binding checks (one vote per chain per operation)
    """
    
    ARGUMENT = 'chainid-binding'
    HELP = 'Missing ChainId binding enforcement'
    IMPACT = DetectorClassification.HIGH
    CONFIDENCE = DetectorClassification.MEDIUM

    WIKI = 'https://github.com/Chronos-Vault/trinity-protocol/wiki/ChainId-Binding'
    WIKI_TITLE = 'ChainId Binding Requirement'
    WIKI_DESCRIPTION = 'Each chain must vote exactly once per operation'
    WIKI_EXPLOIT_SCENARIO = 'Without ChainId binding, same chain can vote multiple times'
    WIKI_RECOMMENDATION = 'Check hasVoted[operationId][chainId] before accepting proof'

    def _detect(self):
        results = []
        
        for contract in self.compilation_unit.contracts_derived:
            if 'CrossChain' in contract.name or 'Bridge' in contract.name:
                # Find proof submission functions
                for func in contract.functions:
                    if 'submitProof' in func.name or 'verifyProof' in func.name:
                        # Check for ChainId binding check
                        has_chainid_check = False
                        for node in func.nodes:
                            if 'hasVoted' in str(node) or 'chainVerified' in str(node):
                                has_chainid_check = True
                                break
                        
                        if not has_chainid_check:
                            info = [
                                'Function ',
                                func,
                                ' does not check ChainId binding (hasVoted mapping)\n',
                                'Risk: Same chain can submit multiple proofs for same operation\n'
                            ]
                            res = self.generate_result(info)
                            results.append(res)
        
        return results


class HTLCAtomicityDetector(AbstractDetector):
    """
    Detects potential HTLC atomicity violations (claim vs refund mutual exclusion)
    """
    
    ARGUMENT = 'htlc-atomicity'
    HELP = 'HTLC claim/refund mutual exclusion violations'
    IMPACT = DetectorClassification.HIGH
    CONFIDENCE = DetectorClassification.MEDIUM

    WIKI = 'https://github.com/Chronos-Vault/trinity-protocol/wiki/HTLC'
    WIKI_TITLE = 'HTLC Atomicity Requirement'
    WIKI_DESCRIPTION = 'HTLCs must enforce claim XOR refund (mutual exclusion)'
    WIKI_EXPLOIT_SCENARIO = 'Without mutual exclusion, both claim and refund can execute'
    WIKI_RECOMMENDATION = 'Use claimed/refunded flags to prevent double execution'

    def _detect(self):
        results = []
        
        for contract in self.compilation_unit.contracts_derived:
            if 'HTLC' in contract.name or 'AtomicSwap' in contract.name:
                has_claim = False
                has_refund = False
                has_mutual_exclusion = False
                
                # Find claim and refund functions
                for func in contract.functions:
                    if 'claim' in func.name.lower():
                        has_claim = True
                        # Check for mutual exclusion check
                        for node in func.nodes:
                            if 'refunded' in str(node) or 'claimed' in str(node):
                                has_mutual_exclusion = True
                    
                    if 'refund' in func.name.lower():
                        has_refund = True
                
                # Alert if HTLC pattern detected without mutual exclusion
                if has_claim and has_refund and not has_mutual_exclusion:
                    info = [
                        'Contract ',
                        contract,
                        ' has claim/refund functions without mutual exclusion check\n',
                        'Risk: Both claim and refund could execute (double-spend)\n'
                    ]
                    res = self.generate_result(info)
                    results.append(res)
        
        return results


class TimelockBypassDetector(AbstractDetector):
    """
    Detects potential timelock bypass vulnerabilities
    """
    
    ARGUMENT = 'timelock-bypass'
    HELP = 'Timelock bypass vulnerabilities'
    IMPACT = DetectorClassification.HIGH
    CONFIDENCE = DetectorClassification.MEDIUM

    WIKI = 'https://github.com/Chronos-Vault/trinity-protocol/wiki/Timelocks'
    WIKI_TITLE = 'Timelock Bypass Detection'
    WIKI_DESCRIPTION = 'All time-locked operations must check block.timestamp'
    WIKI_EXPLOIT_SCENARIO = 'Owner can bypass timelock if not enforced in all code paths'
    WIKI_RECOMMENDATION = 'Ensure all withdrawal/execution paths check timelock'

    def _detect(self):
        results = []
        
        for contract in self.compilation_unit.contracts_derived:
            # Find timelock variables
            timelock_vars = []
            for var in contract.state_variables:
                if 'unlockTime' in var.name or 'executionTime' in var.name or 'timelocked' in var.name.lower():
                    timelock_vars.append(var)
            
            if timelock_vars:
                # Find execution functions
                for func in contract.functions:
                    if func.visibility in ['public', 'external']:
                        if any(keyword in func.name.lower() for keyword in ['withdraw', 'execute', 'claim', 'release']):
                            # Check if function checks timelock
                            checks_timelock = False
                            for node in func.nodes:
                                node_str = str(node)
                                if 'block.timestamp' in node_str and any(var.name in node_str for var in timelock_vars):
                                    checks_timelock = True
                                    break
                            
                            if not checks_timelock and not func.is_constructor:
                                info = [
                                    'Function ',
                                    func,
                                    ' does not check timelock before execution\n',
                                    f'Timelock variables: {[v.name for v in timelock_vars]}\n',
                                    'Risk: Timelock can be bypassed\n'
                                ]
                                res = self.generate_result(info)
                                results.append(res)
        
        return results


class MultiSigThresholdDetector(AbstractDetector):
    """
    Detects incorrect multi-sig threshold configurations
    """
    
    ARGUMENT = 'multisig-threshold'
    HELP = 'Multi-sig threshold configuration issues'
    IMPACT = DetectorClassification.MEDIUM
    CONFIDENCE = DetectorClassification.HIGH

    WIKI = 'https://github.com/Chronos-Vault/trinity-protocol/wiki/MultiSig'
    WIKI_TITLE = 'Multi-Sig Threshold Validation'
    WIKI_DESCRIPTION = 'Multi-sig threshold must be reasonable (2-of-3, 3-of-5, etc)'
    WIKI_EXPLOIT_SCENARIO = 'Threshold = 1 defeats purpose of multi-sig'
    WIKI_RECOMMENDATION = 'Ensure threshold >= 2 and threshold <= signer count'

    def _detect(self):
        results = []
        
        for contract in self.compilation_unit.contracts_derived:
            if 'MultiSig' in contract.name or 'MultiSignature' in contract.name:
                # Find threshold and signer variables
                threshold_var = None
                signer_count = 0
                
                for var in contract.state_variables:
                    if 'threshold' in var.name.lower():
                        threshold_var = var
                    if 'signer' in var.name.lower():
                        signer_count += 1
                
                if threshold_var:
                    # Check if threshold is validated
                    constructor = None
                    for func in contract.functions:
                        if func.is_constructor:
                            constructor = func
                            break
                    
                    if constructor:
                        validates_threshold = False
                        for node in constructor.nodes:
                            node_str = str(node)
                            if 'require' in node_str and threshold_var.name in node_str:
                                validates_threshold = True
                                break
                        
                        if not validates_threshold:
                            info = [
                                'Constructor of ',
                                contract,
                                ' does not validate multi-sig threshold\n',
                                'Risk: Threshold could be 0 or exceed signer count\n',
                                'Recommendation: require(threshold >= 2 && threshold <= signerCount)\n'
                            ]
                            res = self.generate_result(info)
                            results.append(res)
        
        return results


# Register all custom detectors
def make_plugin():
    """
    Plugin entry point for Slither
    Usage: slither . --detect trinity-consensus,chainid-binding,htlc-atomicity,timelock-bypass,multisig-threshold
    """
    return [
        TrinityConsensusDetector,
        ChainIdBindingDetector,
        HTLCAtomicityDetector,
        TimelockBypassDetector,
        MultiSigThresholdDetector
    ]
