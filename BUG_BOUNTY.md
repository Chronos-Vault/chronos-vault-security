# Bug Bounty Program

**Trinity Protocol™ Security Bug Bounty**  
Status: **ACTIVE** 🟢  
Version: v3.5.24 | December 2025

---

## Reward Structure

| Severity | Reward Range | Response Time |
|----------|--------------|---------------|
| **Critical** | $25,000 - $100,000 | 24 hours |
| **High** | $10,000 - $25,000 | 48 hours |
| **Medium** | $2,500 - $10,000 | 3-7 days |
| **Low** | $500 - $2,500 | 7-14 days |

**Total Budget:** $500,000 allocated for security research  
**Payment Method:** USDC, ETH, or CVT tokens

---

## Scope

### In Scope

**Smart Contracts:**
- `contracts/ethereum/*.sol` - All Solidity contracts
- `contracts/solana/*.rs` - All Rust programs
- `contracts/ton/*.fc` - All FunC contracts

**Critical Areas:**
- Trinity 2-of-3 consensus mechanism bypass
- Cross-chain message replay attacks
- Validator equivocation without slashing
- Timelock bypass vulnerabilities
- Fund extraction or theft vectors
- Formal verification theorem violations

**Deployed Contracts:**
| Network | Contract | Address |
|---------|----------|---------|
| Arbitrum Sepolia | TrinityProtocol | `0x5E1EE00E5DFa54488AC5052C747B97c7564872F9` |
| Arbitrum Sepolia | TrinityConsensusVerifier | `0x59396D58Fa856025bD5249E342729d5550Be151C` |
| Solana Devnet | TrinityValidator | `CYaDJYRqm35udQ8vkxoajSER8oaniQUcV8Vvw5BqJyo2` |
| TON Testnet | TrinityConsensus | `EQeGlYzwupSROVWGucOmKyUDbSaKmPfIpHHP5mV73odL8` |

### Out of Scope
- Frontend UI/UX issues
- Social engineering attacks
- Third-party dependencies (unless integrated)
- Issues already reported or known
- Theoretical attacks without proof of concept

---

## Submission Process

1. **Email:** security@chronosvault.io
2. **Include:**
   - Detailed vulnerability description
   - Step-by-step reproduction
   - Impact assessment
   - Suggested fix (optional)
3. **Receive acknowledgment** within 24 hours
4. **Collaborate** on fix timeline
5. **Receive payment** after verification

---

## Rules

- Test only on testnets
- Do not access real user funds or data
- Provide sufficient detail for reproduction
- Allow 90 days for fix before disclosure
- One submission per vulnerability

---

## Hall of Fame

Security researchers who help protect Trinity Protocol will be recognized in our Hall of Fame (with permission).

---

**Trust Math, Not Humans** - Help us verify the mathematics.

© 2025 Chronos Vault - Trinity Protocol™
