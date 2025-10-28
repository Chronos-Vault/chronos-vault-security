# Echidna Fuzzing Test Suite for Chronos Vault

## Overview

This directory contains comprehensive Echidna property-based fuzzing tests for the Chronos Vault smart contracts. Echidna runs **10 million+ random transactions** to discover edge cases, invariant violations, and security vulnerabilities that traditional tests might miss.

## What is Echidna?

Echidna is a property-based fuzzer for Ethereum smart contracts that:
- Generates **millions of random transactions** to test invariants
- Uses **coverage-guided fuzzing** to maximize code path exploration
- Automatically **shrinks failing test cases** to minimal reproducible examples
- Tests **mathematical invariants** that should NEVER be violated

## Test Suites

### 1. ChronosVault.echidna.sol
Tests the main vault contract with time-lock and multi-sig functionality.

**Critical Invariants Tested:**
- ✅ `echidna_balance_never_negative` - Vault balance never goes negative
- ✅ `echidna_timelock_enforced` - Withdrawals blocked before unlock time
- ✅ `echidna_authorization_required` - Only authorized users can withdraw
- ✅ `echidna_multisig_threshold` - Multi-sig threshold (2-of-3) always valid
- ✅ `echidna_security_level_valid` - Security level stays in range 1-5
- ✅ `echidna_supply_conservation` - Total supply equals deposits minus withdrawals
- ✅ `echidna_crosschain_verification` - Cross-chain verification enforced for security level 3+

**Random Operations:**
- Deposits, withdrawals, redeems
- Multi-sig requests, approvals, executions
- Security level changes
- Cross-chain verification
- Emergency recovery attempts

### 2. EmergencyMultiSig.echidna.sol
Tests the emergency multi-signature consensus system.

**Critical Invariants Tested:**
- ✅ `echidna_two_of_three_required` - 2-of-3 threshold always enforced
- ✅ `echidna_timelock_48h` - 48-hour timelock always enforced
- ✅ `echidna_no_double_execution` - Proposals execute once only
- ✅ `echidna_signers_unique` - All signers are unique and non-zero
- ✅ `echidna_signature_count_max_three` - Never more than 3 signatures
- ✅ `echidna_executed_requires_consensus` - Executed proposals always have 2+ signatures
- ✅ `echidna_execution_count_valid` - Executed count ≤ created count

**Random Operations:**
- Proposal creation, signing, execution
- Early execution attempts (should fail)
- Double signing attempts (should fail)
- Proposal cancellation
- Replay attack attempts

### 3. CrossChainBridge.echidna.sol
Tests the Trinity Protocol multi-chain consensus system.

**Critical Invariants Tested:**
- ✅ `echidna_trinity_consensus` - 2-of-3 consensus always enforced
- ✅ `echidna_one_vote_per_chain` - Each chain votes exactly once per operation
- ✅ `echidna_replay_protection` - Signatures used once only
- ✅ `echidna_max_three_proofs` - Never more than 3 proofs per operation
- ✅ `echidna_completed_requires_consensus` - Completed operations always have 2+ proofs
- ✅ `echidna_circuit_breaker_blocks_operations` - Circuit breaker blocks new operations
- ✅ `echidna_fee_integrity` - Collected fees never negative
- ✅ `echidna_operation_count_valid` - Completed count ≤ created count
- ✅ `echidna_valid_chain_ids` - Only valid chain IDs (1=Ethereum, 2=Solana, 3=TON)

**Random Operations:**
- Operation creation with various amounts/priorities
- Chain proof submissions from different chains
- Double proof attempts (should fail)
- Operation execution
- Circuit breaker triggers
- Emergency pause/resume
- Validator management
- Fee distribution and claiming
- Signature replay attempts

## Running Echidna Tests

### Prerequisites
```bash
# Install Echidna (macOS)
brew install echidna

# Install Echidna (Linux)
wget https://github.com/crytic/echidna/releases/latest/download/echidna-x86_64-linux.tar.gz
tar -xzf echidna-x86_64-linux.tar.gz
sudo mv echidna /usr/local/bin/

# Install Echidna (via Docker)
docker pull trailofbits/eth-security-toolbox
```

### Run All Tests
```bash
# Run ChronosVault fuzzing (10M iterations)
echidna . --contract ChronosVaultEchidna --config test/echidna/echidna.yaml

# Run EmergencyMultiSig fuzzing (10M iterations)
echidna . --contract EmergencyMultiSigEchidna --config test/echidna/echidna.yaml

# Run CrossChainBridge fuzzing (10M iterations)
echidna . --contract CrossChainBridgeEchidna --config test/echidna/echidna.yaml
```

### Run with Coverage
```bash
# Generate coverage report
echidna . --contract ChronosVaultEchidna --config test/echidna/echidna.yaml --coverage
```

### Quick Test (1M iterations)
```bash
# Faster testing for development
echidna . --contract ChronosVaultEchidna --test-limit 1000000
```

## Interpreting Results

### ✅ Test Passed
```
echidna_balance_never_negative: passed! 🎉
```
**Meaning:** After 10M random transactions, the invariant was NEVER violated. The property is mathematically sound.

### ❌ Test Failed
```
echidna_balance_never_negative: failed!💥  
  Call sequence:
    depositRandom(1000000000000000000)
    withdrawRandom(2000000000000000000)
```
**Meaning:** Echidna found a way to break the invariant. The call sequence shows the exact steps to reproduce the bug.

**Action Required:**
1. Analyze the failing call sequence
2. Identify the root cause in the contract
3. Fix the vulnerability
4. Re-run Echidna to confirm the fix

### 🔍 Shrinking
```
Shrinking...
  Original: 100 calls
  Shrunk to: 3 calls
```
**Meaning:** Echidna automatically reduces the failing test case to the minimal number of calls needed to reproduce the bug.

## Configuration (echidna.yaml)

```yaml
testMode: assertion          # Use assertion-based testing
testLimit: 10000000          # 10 million iterations
shrinkLimit: 5000            # Shrink failing tests up to 5000 times
seqLen: 100                  # Max 100 calls per test sequence
coverage: true               # Enable coverage-guided fuzzing
corpusDir: "corpus"          # Save interesting test cases
```

## Expected Runtime

- **10M iterations:** ~30-60 minutes per contract
- **1M iterations (quick test):** ~3-6 minutes per contract
- **Coverage analysis:** +10-20% time overhead

## Corpus Directory

Echidna saves interesting test cases to `corpus/` for:
- **Regression testing** - Replay discovered edge cases
- **Mutation fuzzing** - Generate new tests from successful ones
- **CI/CD integration** - Fast sanity checks

## Best Practices

### 1. Always Use `try/catch` for Fuzz Operations
```solidity
function withdrawRandom(uint256 amount) public {
    try vault.withdraw(amount) {
        // Success
    } catch {
        // Expected failure (e.g., time-lock not expired)
    }
}
```

### 2. Name Properties with `echidna_*` Prefix
```solidity
function echidna_balance_never_negative() public view returns (bool) {
    return vault.balance() >= 0;
}
```

### 3. Keep Invariants Simple
```solidity
// ✅ GOOD: Simple, clear invariant
function echidna_threshold_valid() public view returns (bool) {
    return threshold > 0 && threshold <= signers.length;
}

// ❌ BAD: Complex, hard to debug
function echidna_complex_check() public view returns (bool) {
    return checkA() && checkB() && checkC() && checkD();
}
```

### 4. Use Bounded Random Values
```solidity
function depositRandom(uint256 amount) public {
    amount = amount % 1000 ether + 1; // Limit to reasonable range
    vault.deposit(amount);
}
```

### 5. Track State for Invariant Checking
```solidity
uint256 public totalDeposits;
uint256 public totalWithdrawals;

function echidna_supply_conservation() public view returns (bool) {
    return vault.balance() <= totalDeposits - totalWithdrawals;
}
```

## Troubleshooting

### Echidna Hangs or Runs Forever
**Solution:** Reduce `testLimit` or `seqLen` in `echidna.yaml`

### Too Many False Positives
**Solution:** Tighten invariant conditions or add state tracking

### No Coverage of Critical Code Paths
**Solution:** Add more fuzz operations that trigger those paths

### Out of Memory
**Solution:** Reduce `testLimit` or use `--rpc-url` to run against a node

## Integration with CI/CD

### GitHub Actions Example
```yaml
name: Echidna Fuzzing

on: [push, pull_request]

jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Run Echidna
        run: |
          docker run -v $PWD:/src trailofbits/eth-security-toolbox \
            echidna /src --contract ChronosVaultEchidna --test-limit 1000000
```

## Resources

- **Echidna Documentation:** https://github.com/crytic/echidna
- **Property-Based Testing Guide:** https://blog.trailofbits.com/property-testing
- **Echidna Tutorial:** https://secure-contracts.com/program-analysis/echidna

## Security Contact

If Echidna discovers a critical vulnerability, please report it responsibly:
- **Email:** security@chronosvault.org
- **Bug Bounty:** https://chronosvault.org/bug-bounty

---

**Remember:** Echidna is a powerful tool, but it's not a replacement for formal audits. Use it as part of a comprehensive security strategy that includes:
- ✅ Unit tests (Hardhat/Foundry)
- ✅ Integration tests
- ✅ Echidna property-based fuzzing (this)
- ✅ Formal verification (Lean 4, Certora)
- ✅ Professional security audits (OpenZeppelin, Trail of Bits)

**Happy Fuzzing! 🐝**
