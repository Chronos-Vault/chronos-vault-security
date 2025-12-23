# Trinity Protocol™ - ZK-SNARK Circuits

**Version:** v3.5.24  
**Status:** Production Ready  
**Last Updated:** December 2025

---

## Overview

Zero-knowledge proof circuits for privacy-preserving operations in Trinity Protocol.

---

## Circuits

### 1. multisig_verification.circom
Privacy-preserving k-of-n threshold signature verification.

**Purpose:** Prove that k validators signed without revealing which k.

### 2. vault_ownership.circom
Zero-knowledge vault ownership proofs.

**Purpose:** Prove vault ownership without revealing private keys.

---

## On-Chain Verifiers

| Contract | Purpose |
|----------|---------|
| `Groth16Verifier.sol` | Core BN254 Groth16 proof verification |
| `ZKConsensusVerifier.sol` | Trinity 2-of-3 ZK consensus integration |
| `IZKVerifier.sol` | Interface for ZK verification |

These contracts are in `contracts/ethereum/`.

---

## Build Instructions

```bash
# Make build script executable
chmod +x build.sh

# Build all circuits
./build.sh

# Build single circuit
./build.sh multisig_verification

# Generate witness (for testing)
./build.sh witness multisig_verification test_inputs/multisig_input.json

# Generate proof
./build.sh prove multisig_verification

# Verify proof
./build.sh verify multisig_verification
```

---

## Requirements

- circom >= 2.1.0
- snarkjs
- Node.js >= 18

```bash
npm install -g circom snarkjs
```

---

## Test Inputs

Sample test inputs are in `test_inputs/`:
- `multisig_input.json` - Multi-sig verification test
- `vault_input.json` - Vault ownership test

---

## Circuit Statistics

| Metric | Value |
|--------|-------|
| Constraints | ~850 |
| Proof Generation | 5-20ms |
| Verification | 2-10ms |
| Proof Size | 128 bytes |
| Security | 128-bit (BN254) |

---

## Integration with Trinity Protocol

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Arbitrum   │     │   Solana    │     │     TON     │
│  Validator  │     │  Validator  │     │  Validator  │
└──────┬──────┘     └──────┬──────┘     └──────┬──────┘
       │                   │                   │
       └───────────┬───────┴───────────────────┘
                   │
                   ▼
         ┌─────────────────┐
         │  ZK Proof Gen   │
         │  (off-chain)    │
         └────────┬────────┘
                  │
                  ▼
         ┌─────────────────┐
         │ ZKConsensusVerifier │
         │  (on-chain)     │
         └─────────────────┘
```

---

**Trust Math, Not Humans**

© 2025 Chronos Vault - Trinity Protocol™
