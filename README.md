# Trinity Protocol Security Proofs

Formal verification proofs for Trinity Protocol smart contracts using Lean4.

## Verified Contracts

### Ethereum/Arbitrum
- ChronosVault.lean - ERC-4626 compliant vault operations
- HTLC.lean - Hash Time-Locked Contracts for atomic swaps
- TrinityShield.lean - Hardware TEE verification (SGX/SEV)
- KeeperRegistry.lean - Keeper management and staking
- Relayer.lean - Cross-chain message relaying
- Governance.lean - Timelock governance proposals
- FeeSplitter.lean - Fee distribution logic
- ExitGateway.lean - Cross-chain exit mechanism
- EmergencyMultiSig.lean - Emergency multi-signature actions
- CrossChainBridge.lean - Cross-chain messaging

### Solana
- Solana/TrinityValidator.lean - Consensus validation on Solana
- Solana/ChronosVault.lean - Solana vault operations

### TON
- TON/TrinityConsensus.lean - Quantum-resistant consensus
- TON/ChronosVault.lean - TON vault with jetton support
- TON/CrossChainBridge.lean - TON cross-chain bridge

## Key Properties Proved

1. **Consensus Safety** - 2-of-3 validator agreement required
2. **Timelock Enforcement** - Governance delays cannot be bypassed
3. **Value Conservation** - Assets preserved through operations
4. **Solvency Invariants** - Vault remains solvent after operations
5. **Nonce Security** - Replay attack prevention
6. **Quantum Resistance** - ML-KEM-1024 and Dilithium-5 properties

## Building

```bash
cd lean4-proofs
lake build
```

## Deployed Contracts

| Network | Contract | Address |
|---------|----------|---------|
| Arbitrum Sepolia | TrinityConsensusVerifier | 0x59396D58Fa856025bD5249E342729d5550Be151C |
| Arbitrum Sepolia | HTLCChronosBridge | 0x82C3AbF6036cEE41E151A90FE00181f6b18af8ca |
| Solana Devnet | TrinityValidator | CYaDJYRqm35udQ8vkxoajSER8oaniQUcV8Vvw5BqJyo2 |
| TON Testnet | TrinityConsensus | EQeGlYzwupSROVWGucOmKyUDbSaKmPfIpHHP5mV73odL8 |

## License

MIT License - Chronos Vault
