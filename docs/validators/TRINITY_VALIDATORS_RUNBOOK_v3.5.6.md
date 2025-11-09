# Trinity Protocol v3.5.6 Validators Operational Runbook

**Contract Version**: v3.5.6  
**Contract**: TrinityConsensusVerifier.sol  
**Last Updated**: November 9, 2025  
**Security Audit**: COMPLETE - All critical and high vulnerabilities fixed

---

## 🎯 Executive Summary

This runbook provides operational procedures for validators managing the TrinityConsensusVerifier smart contract. It covers emergency procedures, key rotation, Merkle root updates, monitoring, and security best practices.

**Security Status**: ✅ Production-Ready (all C/H severity issues resolved)

---

## 🔐 Security Fixes in v3.5.6

Trinity v3.5.6 includes comprehensive security fixes from the security audit:

### CRITICAL Fixes
- **C-1**: Merkle proof depth validation (gas griefing protection)
- **C-2**: Balance invariant validation across ALL accounting functions
- **C-3**: Strict Checks-Effects-Interactions pattern in cancellation functions

### HIGH Fixes
- **H-1**: Vault ETH reception validation (prevents stuck funds)
- **H-3**: ChainId validation in Merkle proof submission
- **H-5**: ChainId field in MerkleRootProposal struct (verified)

### MEDIUM Fixes
- **M-1**: Fee beneficiary update function (key rotation)

---

## 👥 Validator Roles & Responsibilities

### Emergency Controller
**Address**: Configured at deployment  
**Capabilities**:
- Emergency pause/unpause contract
- Emergency operation cancellation
- Fee withdrawal to treasury
- Fee beneficiary rotation (M-1)
- Emergency controller transfer

**Security**: This is the MOST PRIVILEGED role. Use multi-signature wallet (Gnosis Safe) with 3-of-5 threshold.

### Chain Validators (3 total)
1. **Arbitrum Validator** (ChainId: 1)
2. **Solana Validator** (ChainId: 2)
3. **TON Validator** (ChainId: 3)

**Capabilities**:
- Submit Merkle proofs for operations
- Propose validator rotations
- Propose Merkle root updates
- Confirm proposals (2-of-3 consensus required)

**Security**: Each validator MUST be operated by different entities for true decentralization.

---

## 🚨 Emergency Procedures

### 1. Emergency Pause (Circuit Breaker)

**When to Use**:
- Smart contract exploit detected
- Abnormal operation volume spike
- Validator compromise suspected
- Critical bug discovered

**Procedure**:
```solidity
// Emergency Controller executes
await trinityVerifier.pause();
```

**Effects**:
- ❌ All user operations blocked (createOperation)
- ✅ Emergency controller can still: cancel operations, withdraw fees, rotate keys
- ✅ Users can claim failed fees

**Monitoring**: Watch for `Paused(address account)` event

---

### 2. Emergency Resume

**When to Use**:
- Incident resolved and verified
- Security patches deployed
- System integrity restored

**Procedure**:
```solidity
// Emergency Controller executes
await trinityVerifier.unpause();
```

**Verification**:
1. Check paused state: `await trinityVerifier.paused()` → should return `false`
2. Test operation creation with small amount
3. Verify consensus mechanism working (2-of-3 proofs)

**Monitoring**: Watch for `Unpaused(address account)` event

---

### 3. Emergency Operation Cancellation

**When to Use**:
- Fraudulent operation detected
- User reports unauthorized operation
- Exploit attempt identified

**Procedure**:
```solidity
// Emergency Controller executes
await trinityVerifier.emergencyCancelOperation(operationId);
```

**Security** (v3.5.6 C-3 FIX):
- ✅ Strict CEI pattern enforced
- ✅ State updated BEFORE refund
- ✅ Immediate revert on failed refund (no double-counting)
- ✅ Balance invariant validated

**Monitoring**: Watch for `OperationCancelled` event

---

## 🔄 Validator Rotation Procedures

### When to Rotate Validators

**Required**:
- Validator key compromised
- Validator operator change
- Security incident

**Recommended**:
- Every 90 days (routine key rotation)
- Infrastructure upgrades
- Organizational changes

### Rotation Process (2-of-3 Consensus Required)

**Step 1: Propose Rotation**
```solidity
// Any validator can propose rotation
await trinityVerifier.proposeValidatorRotation(
  chainId,           // 1=Arbitrum, 2=Solana, 3=TON
  oldValidatorAddress,
  newValidatorAddress
);
```

**Step 2: Confirm Proposal (2 Different Validators)**
```solidity
// Second validator confirms
await trinityVerifier.confirmValidatorRotation(proposalId);

// Third validator confirms (reaches 2-of-3 threshold)
await trinityVerifier.confirmValidatorRotation(proposalId);
```

**Step 3: Automatic Execution**
- Proposal auto-executes when 2-of-3 confirmations reached
- Old validator deauthorized
- New validator authorized

**Security Validations** (v3.5.4):
- ✅ All 3 validators must be UNIQUE addresses (prevents single entity control)
- ✅ Validators cannot confirm their own proposals (H-2 fix)
- ✅ Proposal expires after 7 days if not executed

**Monitoring**: 
- `ValidatorRotationProposed(proposalId, chainId, oldValidator, newValidator)`
- `ValidatorRotationConfirmed(proposalId, validator, confirmations)`
- `ValidatorRotationExecuted(proposalId, chainId, oldValidator, newValidator)`

---

## 🌳 Merkle Root Update Procedures

### When to Update Merkle Roots

**Required**:
- New batch of operations processed
- Cross-chain proof verification needed
- State synchronization with off-chain systems

### Update Process (2-of-3 Consensus Required)

**Step 1: Propose Merkle Root Update**
```solidity
// Any validator proposes new root with MANDATORY chainId
await trinityVerifier.proposeMerkleUpdate(
  chainId,        // 1=Arbitrum, 2=Solana, 3=TON (REQUIRED v3.5.5 H-3 FIX)
  newMerkleRoot,
  newNonce        // Increments for replay protection
);
```

**Security** (v3.5.5 H-3 FIX):
- ✅ ChainId MUST match proposal's chainId
- ✅ Prevents cross-chain proof replay attacks
- ✅ Nonce incremented to prevent replay

**Step 2: Confirm Update (2 Different Validators)**
```solidity
// Second validator confirms (chainId MUST match proposal)
await trinityVerifier.confirmMerkleUpdate(proposalId, chainId);

// Third validator confirms (reaches 2-of-3, auto-executes)
await trinityVerifier.confirmMerkleUpdate(proposalId, chainId);
```

**Verification**:
```solidity
// Check updated Merkle root
bytes32 currentRoot = await trinityVerifier.getMerkleRoot(chainId);
uint256 currentNonce = await trinityVerifier.merkleNonces(chainId);
```

**Monitoring**:
- `MerkleUpdateProposed(proposalId, chainId, newRoot)`
- `MerkleUpdateConfirmed(proposalId, validator, confirmations)`
- `MerkleUpdateExecuted(proposalId, chainId, newRoot)`

---

## 💰 Treasury Management

### Fee Withdrawal (Emergency Controller Only)

**Procedure**:
```solidity
// Emergency Controller withdraws collected fees
await trinityVerifier.withdrawFees(amount);
```

**Security** (v3.5.5 C-2 FIX):
- ✅ Balance invariant validated BEFORE and AFTER withdrawal
- ✅ Reserves ETH for failed fees + pending deposits
- ✅ Reverts if insufficient fees available

**Validation**:
```solidity
// Check available fees
uint256 available = await trinityVerifier.collectedFees();

// Calculate required reserves
uint256 failedFees = await trinityVerifier.totalFailedFees();
uint256 pendingDeposits = await trinityVerifier.totalPendingDeposits();
uint256 reserves = failedFees + pendingDeposits;

// Ensure withdrawal doesn't violate invariant
// contract.balance >= collectedFees + totalFailedFees + totalPendingDeposits
```

**Monitoring**: `FeesWithdrawn(beneficiary, amount)`

---

### Fee Beneficiary Rotation (M-1 - NEW in v3.5.6)

**When to Rotate**:
- Treasury key rotation schedule (every 90 days recommended)
- Treasury address compromise
- Organizational changes

**Procedure**:
```solidity
// Emergency Controller updates fee beneficiary
await trinityVerifier.updateFeeBeneficiary(newBeneficiaryAddress);
```

**Security**:
- ✅ Only Emergency Controller can update
- ✅ Zero-address validation (reverts if address(0))
- ✅ Event emitted for on-chain auditability
- ✅ No pause gating (can rotate during incidents)

**Verification**:
```solidity
// Verify new beneficiary
address current = await trinityVerifier.feeBeneficiary();
console.log("Current fee beneficiary:", current);
```

**Monitoring**: `FeeBeneficiaryUpdated(oldBeneficiary, newBeneficiary)`

**Best Practices**:
1. Use multi-signature wallet for new beneficiary (Gnosis Safe 3-of-5)
2. Test with small withdrawal first
3. Document rotation in security log
4. Update monitoring systems to track new address
5. Rotate keys every 90 days (never reuse old addresses)

---

## 📊 Monitoring & Event Tracking

### Critical Events to Monitor

#### Operation Lifecycle
```solidity
event OperationCreated(bytes32 indexed operationId, address indexed user, OperationType operationType, uint256 amount);
event ChainConfirmation(bytes32 indexed operationId, uint8 indexed chainId, address validator);
event OperationExecuted(bytes32 indexed operationId, address indexed user, uint256 amount);
event OperationCancelled(bytes32 indexed operationId, address indexed user, uint256 refund);
```

#### Consensus & Proofs
```solidity
event MerkleRootUpdated(uint8 indexed chainId, bytes32 oldRoot, bytes32 newRoot, uint256 nonce);
event ValidatorRotationProposed(bytes32 indexed proposalId, uint8 chainId, address oldValidator, address newValidator);
event ValidatorRotationExecuted(bytes32 indexed proposalId, uint8 chainId, address oldValidator, address newValidator);
```

#### Emergency & Security
```solidity
event Paused(address indexed account);
event Unpaused(address indexed account);
event EmergencyControlTransferred(address indexed oldController, address indexed newController);
event FeeBeneficiaryUpdated(address indexed oldBeneficiary, address indexed newBeneficiary); // v3.5.6
```

#### Treasury & Fees
```solidity
event FeesWithdrawn(address indexed beneficiary, uint256 amount);
event FailedFeeClaimed(address indexed user, uint256 amount);
event FailedFeeRecorded(address indexed user, uint256 amount);
```

### Alerting Thresholds

| Metric | Warning | Critical | Action |
|--------|---------|----------|---------|
| Failed fee claims | > 5/day | > 20/day | Investigate refund mechanism |
| Emergency cancellations | > 1/day | > 5/day | Check for exploit attempts |
| Paused state | > 1 hour | > 6 hours | Expedite incident resolution |
| Balance invariant violations | 1 occurrence | 1 occurrence | IMMEDIATE pause + investigation |
| Validator rotation failures | > 1/week | > 3/week | Check validator coordination |

### Health Check Queries

**Contract State**:
```solidity
// Check if paused
bool isPaused = await trinityVerifier.paused();

// Check validator addresses
address arbValidator = await trinityVerifier.validators(1); // Arbitrum
address solValidator = await trinityVerifier.validators(2); // Solana
address tonValidator = await trinityVerifier.validators(3); // TON

// Check emergency controller
address emergency = await trinityVerifier.emergencyController();

// Check fee beneficiary
address beneficiary = await trinityVerifier.feeBeneficiary();
```

**Balance Invariant** (v3.5.6 C-2):
```solidity
// Verify invariant: balance >= collectedFees + totalFailedFees + totalPendingDeposits
uint256 balance = await ethers.provider.getBalance(trinityVerifierAddress);
uint256 collected = await trinityVerifier.collectedFees();
uint256 failed = await trinityVerifier.totalFailedFees();
uint256 pending = await trinityVerifier.totalPendingDeposits();

uint256 required = collected + failed + pending;
console.log("Balance:", ethers.formatEther(balance));
console.log("Required:", ethers.formatEther(required));
console.log("Invariant Valid:", balance >= required);
```

---

## 🔒 Security Best Practices

### Validator Operations

**DO**:
- ✅ Run each validator on separate infrastructure
- ✅ Use hardware wallets for production validator keys
- ✅ Implement multi-signature for emergency controller (Gnosis Safe 3-of-5)
- ✅ Rotate keys every 90 days
- ✅ Monitor all events in real-time
- ✅ Test on testnet before mainnet execution
- ✅ Maintain validator runbook access 24/7

**DON'T**:
- ❌ Store multiple validator keys on same server
- ❌ Share validator keys between team members
- ❌ Reuse keys across environments
- ❌ Execute emergency actions without verification
- ❌ Ignore warning alerts

### Proposal Verification

Before confirming any proposal:
1. Verify proposal details match intention
2. Check proposalId corresponds to correct proposal
3. Ensure 2-of-3 consensus is legitimate (not compromised)
4. Test on testnet first (if time permits)
5. Document proposal in security log

### Emergency Response

**Incident Response Time**:
- CRITICAL (exploit detected): < 5 minutes to pause
- HIGH (abnormal activity): < 30 minutes to investigate
- MEDIUM (failed operations): < 2 hours to resolve

**Post-Incident**:
1. Document incident timeline
2. Root cause analysis
3. Update security procedures
4. Notify stakeholders
5. Deploy fixes (if needed)
6. Resume operations only after verification

---

## 🧪 Testing Procedures

### Pre-Deployment Testing

**Testnet Validation**:
```bash
# Deploy to Arbitrum Sepolia
npx hardhat run scripts/deploy-trinity.ts --network arbitrumSepolia

# Run integration tests
npx hardhat test test/integration/trinity-verifier.test.ts
```

**Security Validations**:
1. Test balance invariant under all scenarios
2. Verify CEI pattern in cancellation functions
3. Test Merkle proof depth validation (C-1 fix)
4. Test vault ETH reception validation (H-1 fix)
5. Test fee beneficiary rotation (M-1)
6. Test emergency pause/unpause
7. Test validator rotation (2-of-3 consensus)

### Production Smoke Tests

After deployment:
```solidity
// 1. Create test operation (small amount)
const tx = await trinityVerifier.createOperation(...);

// 2. Submit 2-of-3 Merkle proofs
await trinityVerifier.submitArbitrumProof(...);
await trinityVerifier.submitSolanaProof(...);

// 3. Verify execution
const op = await trinityVerifier.getOperation(operationId);
assert(op.status === OperationStatus.EXECUTED);

// 4. Test emergency pause
await trinityVerifier.pause();
assert(await trinityVerifier.paused() === true);

// 5. Test unpause
await trinityVerifier.unpause();
assert(await trinityVerifier.paused() === false);
```

---

## 📋 Operational Checklist

### Daily Operations
- [ ] Monitor validator health (all 3 chains)
- [ ] Check contract balance invariant
- [ ] Review failed fee claims
- [ ] Verify no paused state (unless incident)
- [ ] Check gas balances for all validators

### Weekly Operations
- [ ] Review security event logs
- [ ] Verify Merkle root updates
- [ ] Check consensus proposal activity
- [ ] Test alert systems
- [ ] Backup validator configurations

### Monthly Operations
- [ ] Validator key rotation review
- [ ] Fee beneficiary rotation (if scheduled)
- [ ] Security audit of operations
- [ ] Update runbook (if procedures changed)
- [ ] Disaster recovery drill

### Quarterly Operations (90 days)
- [ ] MANDATORY: Rotate all validator keys
- [ ] MANDATORY: Rotate fee beneficiary address
- [ ] MANDATORY: Rotate emergency controller (if multi-sig)
- [ ] Full security audit review
- [ ] Infrastructure security assessment

---

## 🆘 Troubleshooting

### Balance Invariant Violation

**Error**: `BalanceInvariantViolated(balance, required)`

**Cause**: Contract balance < (collectedFees + totalFailedFees + totalPendingDeposits)

**Resolution**:
1. IMMEDIATELY pause contract
2. Calculate deficit: `required - balance`
3. Investigate accounting discrepancy
4. DO NOT resume until deficit explained
5. Consider emergency fund injection (if legitimate deficit)

### Failed Refund During Cancellation

**Error**: Operation cancelled but fee refund failed

**Behavior** (v3.5.6 C-3 FIX):
- Transaction REVERTS immediately (no state changes persist)
- User can retry cancellation OR claim via `claimFailedFee()`

**Resolution**:
1. User calls `claimFailedFee()` to retrieve fee
2. Verify `FailedFeeClaimed` event emitted
3. Check user balance increased

### Merkle Proof Submission Fails

**Error**: `InvalidMerkleProof(operationId, chainId)` OR `MerkleProofTooDeep(...)`

**Causes**:
- Proof depth > 32 elements (C-1 fix)
- Incorrect Merkle root on chain
- Nonce mismatch (replay protection)
- ChainId mismatch (H-3 fix)

**Resolution**:
1. Verify Merkle root: `getMerkleRoot(chainId)`
2. Check nonce: `merkleNonces[chainId]`
3. Ensure proof depth <= 32 elements
4. Verify chainId matches proposal
5. Regenerate proof with correct parameters

---

## 📞 Emergency Contacts

**Security Incidents**:
- Emergency Controller Multi-Sig: [Gnosis Safe Address]
- Security Team Lead: [Contact]
- On-Call Validator: [24/7 Contact]

**Escalation Path**:
1. On-Call Validator → Security Team Lead
2. Security Team Lead → Emergency Controller
3. Emergency Controller → Executive Team

---

## 📚 Additional Resources

- **Security Audit**: `docs/SECURITY_AUDIT_TRINITY_VERIFIER.md`
- **Contract Documentation**: `contracts/ethereum/TrinityConsensusVerifier.sol`
- **Test Suite**: `test/integration/trinity-verifier.test.ts`
- **Deployment Guide**: `docs/validators/VALIDATOR_SETUP.md`

---

**Last Updated**: November 9, 2025  
**Trinity Protocol v3.5.6**  
**Security Status**: ✅ PRODUCTION-READY (All C/H vulnerabilities fixed)
