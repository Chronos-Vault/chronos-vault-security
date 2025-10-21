# Chronos Vault - ZK-SNARK Circuits

## Overview

This folder contains zero-knowledge proof circuits for advanced privacy features in Chronos Vault.

---

## Important Note: Circuit Breaker vs ZK Circuits

**Are you looking for the Circuit Breaker System?**

The **Circuit Breaker System** (automated anomaly detection) is **NOT in this folder**. It's built into the smart contract:

📍 **Location:** `contracts/ethereum/CrossChainBridgeOptimized.sol` (lines 88-118)

**Circuit Breaker Features:**
- ✅ Automated anomaly detection
- ✅ Volume spike detection (>500% threshold)
- ✅ Failed proof rate monitoring (>20% triggers)
- ✅ Same-block operation limits (>10 triggers)
- ✅ Auto-recovery after 4 hours
- ✅ Emergency manual override

---

## This Folder: ZK-SNARK Circuits

This folder is for **cryptographic circuits** used in zero-knowledge proofs:

### Purpose:
- Privacy-preserving transaction verification
- Zero-knowledge range proofs
- Anonymous vault operations
- Advanced cryptographic features

### Technology Stack:
- **Language:** Circom
- **Proof System:** Groth16
- **Library:** SnarkJS
- **Verification:** On-chain Solidity verifiers

---

## Planned Circuits (Future Development)

### 1. Range Proof Circuit
**File:** `range_proof.circom`  
**Purpose:** Prove amount is within valid range without revealing exact value

### 2. Merkle Tree Inclusion Circuit
**File:** `merkle_inclusion.circom`  
**Purpose:** Prove operation exists in Merkle tree without revealing operation details

### 3. Private Vault Circuit
**File:** `private_vault.circom`  
**Purpose:** Create and manage vaults with zero-knowledge privacy

---

## Status

**Current Status:** 🔨 Under Development

ZK-SNARK circuits are an **optional advanced feature** for privacy-focused users. The core Chronos Vault platform works without them.

**What's Live Now:**
- ✅ Circuit Breaker System (in smart contract)
- ✅ Trinity Protocol 2-of-3 consensus
- ✅ Merkle proof validation
- ✅ Formal verification (Lean 4)

**Coming Soon:**
- ⏳ ZK-SNARK privacy circuits
- ⏳ Anonymous transaction proofs
- ⏳ Zero-knowledge vault operations

---

## Development Timeline

**Phase 1 (Complete):** Core security features ✅  
**Phase 2 (Current):** Production deployment ✅  
**Phase 3 (Q1 2026):** ZK-SNARK privacy features ⏳

---

## For Developers

To contribute ZK-SNARK circuits:

1. Install circom compiler
2. Write circuits in `.circom` files
3. Generate proving/verification keys
4. Create Solidity verifier contracts
5. Integrate with CrossChainBridge

**Resources:**
- Circom documentation: https://docs.circom.io/
- SnarkJS: https://github.com/iden3/snarkjs
- Groth16 paper: https://eprint.iacr.org/2016/260

---

## Questions?

For questions about:
- **Circuit Breaker System** → See smart contract documentation
- **ZK-SNARK Circuits** → Open GitHub issue
- **Privacy Features** → See roadmap in main README

**Repository:** https://github.com/Chronos-Vault/chronos-vault-contracts
