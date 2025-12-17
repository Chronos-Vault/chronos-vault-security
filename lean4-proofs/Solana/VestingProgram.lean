/-
  Solana Vesting Program
  Formal verification of token vesting schedules
-/

import Mathlib.Data.Nat.Basic

namespace Solana.VestingProgram

/-! ## Constants -/

def VESTING_PRECISION : Nat := 10^9
def MIN_VESTING_DURATION : Nat := 2592000    -- 30 days in slots (~400ms/slot)
def MAX_VESTING_DURATION : Nat := 126144000  -- 4 years
def CLIFF_MAX_PERCENT : Nat := 25            -- 25% max at cliff
def REVOCATION_DELAY : Nat := 86400          -- 1 day

/-! ## Vesting Schedule -/

inductive VestingType where
  | linear : VestingType
  | cliff : VestingType
  | milestone : VestingType
deriving DecidableEq, Repr

structure VestingSchedule where
  beneficiary : ByteArray
  totalAmount : Nat
  vestedAmount : Nat
  claimedAmount : Nat
  startSlot : Nat
  endSlot : Nat
  cliffSlot : Option Nat
  cliffAmount : Nat
  vestingType : VestingType
  revocable : Bool
  revoked : Bool
deriving Repr

/-! ## Vesting Calculations -/

def linearVestedAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  if currentSlot < schedule.startSlot then 0
  else if currentSlot ≥ schedule.endSlot then schedule.totalAmount
  else
    let elapsed := currentSlot - schedule.startSlot
    let duration := schedule.endSlot - schedule.startSlot
    (schedule.totalAmount * elapsed) / duration

def cliffVestedAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  match schedule.cliffSlot with
  | some cliff =>
    if currentSlot < cliff then 0
    else if currentSlot ≥ schedule.endSlot then schedule.totalAmount
    else 
      let postCliff := linearVestedAmount schedule currentSlot
      schedule.cliffAmount + postCliff - schedule.cliffAmount
  | none => linearVestedAmount schedule currentSlot

def vestedAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  if schedule.revoked then schedule.vestedAmount
  else match schedule.vestingType with
  | .linear => linearVestedAmount schedule currentSlot
  | .cliff => cliffVestedAmount schedule currentSlot
  | .milestone => schedule.vestedAmount  -- Set manually

def claimableAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  let vested := vestedAmount schedule currentSlot
  if vested > schedule.claimedAmount then vested - schedule.claimedAmount
  else 0

/-! ## Predicates -/

def isActive (schedule : VestingSchedule) (currentSlot : Nat) : Prop :=
  currentSlot ≥ schedule.startSlot ∧ 
  currentSlot < schedule.endSlot ∧
  ¬schedule.revoked

def isFullyVested (schedule : VestingSchedule) (currentSlot : Nat) : Prop :=
  currentSlot ≥ schedule.endSlot ∨ schedule.revoked

def hasCliff (schedule : VestingSchedule) : Prop :=
  schedule.cliffSlot.isSome

def cliffReached (schedule : VestingSchedule) (currentSlot : Nat) : Prop :=
  match schedule.cliffSlot with
  | some cliff => currentSlot ≥ cliff
  | none => True

def canClaim (schedule : VestingSchedule) (currentSlot : Nat) : Prop :=
  claimableAmount schedule currentSlot > 0

def canRevoke (schedule : VestingSchedule) : Prop :=
  schedule.revocable ∧ ¬schedule.revoked

/-! ## State Transitions -/

def claim (schedule : VestingSchedule) (amount : Nat) : VestingSchedule :=
  { schedule with claimedAmount := schedule.claimedAmount + amount }

def revoke (schedule : VestingSchedule) (currentSlot : Nat) : VestingSchedule :=
  { schedule with 
    revoked := true
    vestedAmount := vestedAmount schedule currentSlot
  }

/-! ## Key Theorems -/

theorem min_vesting_30_days : MIN_VESTING_DURATION = 2592000 := rfl

theorem max_vesting_4_years : MAX_VESTING_DURATION = 126144000 := rfl

theorem cliff_max_25_percent : CLIFF_MAX_PERCENT = 25 := rfl

theorem vested_never_exceeds_total (schedule : VestingSchedule) (currentSlot : Nat) :
  vestedAmount schedule currentSlot ≤ schedule.totalAmount := by
  unfold vestedAmount
  split
  · exact Nat.le_refl _  -- revoked case
  · unfold linearVestedAmount
    simp
    sorry -- Requires detailed proof
  · unfold cliffVestedAmount
    simp
    sorry
  · exact Nat.le_refl _

theorem claimed_never_exceeds_vested (schedule : VestingSchedule) (currentSlot : Nat) (amount : Nat) :
  amount ≤ claimableAmount schedule currentSlot →
  let newSchedule := claim schedule amount
  newSchedule.claimedAmount ≤ vestedAmount schedule currentSlot := by
  intro h
  unfold claim claimableAmount at *
  simp
  sorry -- Requires arithmetic proof

theorem linear_vesting_monotonic (schedule : VestingSchedule) (slot1 slot2 : Nat) :
  slot1 ≤ slot2 →
  linearVestedAmount schedule slot1 ≤ linearVestedAmount schedule slot2 := by
  intro h
  unfold linearVestedAmount
  simp
  sorry -- Monotonicity proof

theorem revoke_preserves_vested (schedule : VestingSchedule) (currentSlot : Nat) :
  let revoked := revoke schedule currentSlot
  revoked.vestedAmount = vestedAmount schedule currentSlot := by
  unfold revoke
  rfl

theorem fully_vested_gets_all (schedule : VestingSchedule) (currentSlot : Nat) :
  currentSlot ≥ schedule.endSlot →
  ¬schedule.revoked →
  linearVestedAmount schedule currentSlot = schedule.totalAmount := by
  intro hend _
  unfold linearVestedAmount
  simp [hend]

/-! ## Cliff Validation -/

theorem before_cliff_nothing_vested (schedule : VestingSchedule) (currentSlot : Nat) :
  schedule.vestingType = VestingType.cliff →
  schedule.cliffSlot = some (currentSlot + 1) →
  cliffVestedAmount schedule currentSlot = 0 := by
  intro _ hcliff
  unfold cliffVestedAmount
  simp [hcliff]

end Solana.VestingProgram
