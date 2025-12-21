/-
  ChronosVault - ERC-4626 Compliant Vault
  Formal verification of vault operations with Trinity consensus
  
  Deployed: 0xAE408eC592f0f865bA0012C480E8867e12B4F32D (Arbitrum Sepolia)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic

namespace ChronosVault

/-! ## ERC-4626 Vault Constants -/

def MAX_DEPOSIT : Nat := 2^256 - 1
def MIN_SHARES : Nat := 1000  -- Minimum shares to prevent rounding attacks

/-! ## Vault State -/

structure VaultState where
  totalAssets : Nat
  totalSupply : Nat  -- Total shares
  consensusRequired : Bool
  paused : Bool
  owner : ByteArray
deriving Repr

structure UserPosition where
  shares : Nat
  lastDepositBlock : Nat
deriving Repr

/-! ## Asset-Share Conversion (ERC-4626 Core) -/

def convertToShares (assets : Nat) (state : VaultState) : Nat :=
  if state.totalAssets = 0 || state.totalSupply = 0 then
    assets
  else
    (assets * state.totalSupply) / state.totalAssets

def convertToAssets (shares : Nat) (state : VaultState) : Nat :=
  if state.totalSupply = 0 then
    shares
  else
    (shares * state.totalAssets) / state.totalSupply

/-! ## Deposit/Withdraw Predicates -/

def canDeposit (state : VaultState) (amount : Nat) : Prop :=
  ¬state.paused ∧ amount > 0 ∧ state.totalAssets + amount ≤ MAX_DEPOSIT

def canWithdraw (state : VaultState) (position : UserPosition) (shares : Nat) : Prop :=
  ¬state.paused ∧ shares > 0 ∧ shares ≤ position.shares

def consensusSatisfied (state : VaultState) (confirmations : Nat) : Prop :=
  ¬state.consensusRequired ∨ confirmations ≥ 2

/-! ## State Transitions -/

def deposit (state : VaultState) (assets : Nat) : VaultState × Nat :=
  let shares := convertToShares assets state
  let newState := { state with 
    totalAssets := state.totalAssets + assets
    totalSupply := state.totalSupply + shares 
  }
  (newState, shares)

def withdraw (state : VaultState) (shares : Nat) : VaultState × Nat :=
  let assets := convertToAssets shares state
  let newState := { state with
    totalAssets := state.totalAssets - assets
    totalSupply := state.totalSupply - shares
  }
  (newState, assets)

/-! ## Key Theorems -/

theorem deposit_increases_supply (state : VaultState) (assets : Nat) :
  assets > 0 → 
  let (newState, shares) := deposit state assets
  newState.totalSupply ≥ state.totalSupply := by
  intro h
  unfold deposit
  simp
  exact Nat.le_add_right _ _

theorem withdraw_decreases_supply (state : VaultState) (shares : Nat) :
  shares ≤ state.totalSupply →
  let (newState, _) := withdraw state shares
  newState.totalSupply ≤ state.totalSupply := by
  intro h
  unfold withdraw
  simp
  exact Nat.sub_le _ _

theorem conversion_roundtrip_lower_bound (assets : Nat) (state : VaultState) :
  state.totalAssets > 0 → state.totalSupply > 0 →
  let shares := convertToShares assets state
  let assetsBack := convertToAssets shares state
  assetsBack ≤ assets := by
  intro hassets hsupply
  unfold convertToShares convertToAssets
  simp [hassets, hsupply, Nat.pos_iff_ne_zero.mp]
  -- Integer division property: (a * b / c) * c / b ≤ a for positive b, c
  -- This follows from floor division rounding down:
  -- shares = assets * totalSupply / totalAssets (rounds down)
  -- assetsBack = shares * totalAssets / totalSupply (rounds down again)
  -- 
  -- Let n = assets, s = totalSupply, a = totalAssets
  -- shares = (n * s) / a ≤ n * s / a (exact)
  -- assetsBack = shares * a / s ≤ (n * s / a) * a / s = n * (s * a) / (a * s) = n
  --
  -- The double division only loses value (floors), never gains
  have h1 : (assets * state.totalSupply / state.totalAssets) * state.totalAssets / state.totalSupply ≤ assets := by
    -- Div and mod relationship: n = (n / d) * d + (n % d)
    -- So (n / d) * d ≤ n
    have hdiv1 : assets * state.totalSupply / state.totalAssets * state.totalAssets ≤ assets * state.totalSupply := by
      exact Nat.div_mul_le_self (assets * state.totalSupply) state.totalAssets
    -- Then dividing by totalSupply again
    have hdiv2 : assets * state.totalSupply / state.totalAssets * state.totalAssets / state.totalSupply ≤ 
                 assets * state.totalSupply / state.totalSupply := by
      exact Nat.div_le_div_right hdiv1
    -- And assets * s / s = assets for s > 0
    have hsimp : assets * state.totalSupply / state.totalSupply = assets := by
      exact Nat.mul_div_cancel assets hsupply
    calc (assets * state.totalSupply / state.totalAssets) * state.totalAssets / state.totalSupply 
      ≤ assets * state.totalSupply / state.totalSupply := hdiv2
      _ = assets := hsimp
  exact h1

theorem consensus_required_blocks_unauthorized (state : VaultState) :
  state.consensusRequired → ¬consensusSatisfied state 1 := by
  intro hreq hsat
  unfold consensusSatisfied at hsat
  cases hsat with
  | inl h => exact hreq h
  | inr h => omega

theorem paused_blocks_operations (state : VaultState) (amount : Nat) :
  state.paused → ¬canDeposit state amount := by
  intro hpause
  unfold canDeposit
  intro ⟨hnotpause, _, _⟩
  exact hnotpause hpause

/-! ## Invariants -/

def vaultSolvent (state : VaultState) : Prop :=
  state.totalSupply = 0 ∨ state.totalAssets > 0

theorem deposit_preserves_solvency (state : VaultState) (assets : Nat) :
  vaultSolvent state → assets > 0 →
  let (newState, _) := deposit state assets
  vaultSolvent newState := by
  intro hsolv hassets
  unfold deposit vaultSolvent
  simp
  right
  omega

def noInflation (state : VaultState) : Prop :=
  state.totalSupply > 0 → state.totalAssets > 0 → 
  convertToAssets state.totalSupply state = state.totalAssets

theorem initial_state_solvent : vaultSolvent { 
    totalAssets := 0
    totalSupply := 0
    consensusRequired := true
    paused := false
    owner := ByteArray.empty 
  } := by
  unfold vaultSolvent
  left
  rfl

end ChronosVault
