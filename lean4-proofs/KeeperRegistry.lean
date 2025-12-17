/-
  TrinityKeeperRegistry - Keeper Management
  Formal verification of keeper registration, staking, and slashing
  
  Deployed: 0xAe9bd988011583D87d6bbc206C19e4a9Bda04830 (Arbitrum Sepolia)
-/

import Mathlib.Data.Nat.Basic

namespace KeeperRegistry

/-! ## Constants -/

def MIN_STAKE : Nat := 1000000000000000000  -- 1 ETH
def SLASH_PERCENTAGE : Nat := 10            -- 10%
def UNBONDING_PERIOD : Nat := 604800        -- 7 days
def MAX_KEEPERS : Nat := 100

/-! ## Keeper State -/

inductive KeeperStatus where
  | active : KeeperStatus
  | inactive : KeeperStatus
  | unbonding : KeeperStatus
  | slashed : KeeperStatus
deriving DecidableEq, Repr

structure Keeper where
  address : ByteArray
  stake : Nat
  status : KeeperStatus
  registeredAt : Nat
  lastActivity : Nat
  unbondingStartedAt : Option Nat
  missedTasks : Nat
deriving Repr

structure RegistryState where
  keepers : List Keeper
  totalStaked : Nat
  activeCount : Nat
  paused : Bool
deriving Repr

/-! ## Registration Predicates -/

def canRegister (state : RegistryState) (stake : Nat) : Prop :=
  ¬state.paused ∧ 
  stake ≥ MIN_STAKE ∧ 
  state.activeCount < MAX_KEEPERS

def isActiveKeeper (keeper : Keeper) : Prop :=
  keeper.status = KeeperStatus.active ∧ keeper.stake ≥ MIN_STAKE

def canUnbond (keeper : Keeper) : Prop :=
  keeper.status = KeeperStatus.active

def canWithdraw (keeper : Keeper) (currentTime : Nat) : Prop :=
  keeper.status = KeeperStatus.unbonding ∧
  match keeper.unbondingStartedAt with
  | some t => currentTime ≥ t + UNBONDING_PERIOD
  | none => False

/-! ## State Transitions -/

def register (state : RegistryState) (addr : ByteArray) (stake : Nat) (time : Nat) : RegistryState :=
  let newKeeper : Keeper := {
    address := addr
    stake := stake
    status := KeeperStatus.active
    registeredAt := time
    lastActivity := time
    unbondingStartedAt := none
    missedTasks := 0
  }
  { state with
    keepers := newKeeper :: state.keepers
    totalStaked := state.totalStaked + stake
    activeCount := state.activeCount + 1
  }

def startUnbonding (keeper : Keeper) (time : Nat) : Keeper :=
  { keeper with
    status := KeeperStatus.unbonding
    unbondingStartedAt := some time
  }

def slash (keeper : Keeper) : Keeper :=
  let slashAmount := (keeper.stake * SLASH_PERCENTAGE) / 100
  { keeper with
    stake := keeper.stake - slashAmount
    status := KeeperStatus.slashed
  }

/-! ## Key Theorems -/

theorem register_increases_count (state : RegistryState) (addr : ByteArray) (stake : Nat) (time : Nat) :
  let newState := register state addr stake time
  newState.activeCount = state.activeCount + 1 := by
  unfold register
  rfl

theorem register_increases_stake (state : RegistryState) (addr : ByteArray) (stake : Nat) (time : Nat) :
  let newState := register state addr stake time
  newState.totalStaked = state.totalStaked + stake := by
  unfold register
  rfl

theorem unbonding_preserves_stake (keeper : Keeper) (time : Nat) :
  let unbonding := startUnbonding keeper time
  unbonding.stake = keeper.stake := by
  unfold startUnbonding
  rfl

theorem slash_reduces_stake (keeper : Keeper) :
  keeper.stake > 0 →
  let slashed := slash keeper
  slashed.stake < keeper.stake := by
  intro hpos
  unfold slash
  simp
  sorry -- Requires proof that slashAmount > 0

theorem slashed_status_set (keeper : Keeper) :
  let slashed := slash keeper
  slashed.status = KeeperStatus.slashed := by
  unfold slash
  rfl

/-! ## Stake Requirements -/

theorem min_stake_required (state : RegistryState) (stake : Nat) :
  canRegister state stake → stake ≥ MIN_STAKE := by
  intro h
  unfold canRegister at h
  exact h.2.1

theorem active_has_min_stake (keeper : Keeper) :
  isActiveKeeper keeper → keeper.stake ≥ MIN_STAKE := by
  intro h
  unfold isActiveKeeper at h
  exact h.2

/-! ## Unbonding Period -/

theorem unbonding_period_7_days : UNBONDING_PERIOD = 604800 := rfl

theorem cannot_withdraw_early (keeper : Keeper) (currentTime startTime : Nat) :
  keeper.unbondingStartedAt = some startTime →
  currentTime < startTime + UNBONDING_PERIOD →
  ¬canWithdraw keeper currentTime := by
  intro hstart htime hcan
  unfold canWithdraw at hcan
  simp [hstart] at hcan
  exact Nat.not_le.mpr htime hcan.2

/-! ## Registry Bounds -/

theorem max_keepers_bounded (state : RegistryState) (stake : Nat) :
  canRegister state stake → state.activeCount < MAX_KEEPERS := by
  intro h
  unfold canRegister at h
  exact h.2.2

theorem max_keepers_100 : MAX_KEEPERS = 100 := rfl

end KeeperRegistry
