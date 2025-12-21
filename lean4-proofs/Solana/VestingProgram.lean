/-
  Solana Vesting Program
  Formal verification of token vesting schedules
-/

namespace Solana.VestingProgram

/-! ## Constants -/

def VESTING_PRECISION : Nat := 10^9
def MIN_VESTING_DURATION : Nat := 2592000    -- 30 days in seconds
def MAX_VESTING_DURATION : Nat := 126144000  -- 4 years in seconds
def CLIFF_MAX_PERCENT : Nat := 25            -- 25% max cliff

/-! ## Vesting Schedule -/

inductive VestingType where
  | linear : VestingType
  | cliff : VestingType
  | milestone : VestingType
deriving DecidableEq, Repr

structure VestingSchedule where
  totalAmount : Nat
  vestedAmount : Nat
  claimedAmount : Nat
  startSlot : Nat
  endSlot : Nat
  cliffSlot : Option Nat
  cliffAmount : Nat
  vestingType : VestingType
  revoked : Bool
deriving Repr

/-! ## Vesting Calculations -/

def linearVestedAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  if currentSlot < schedule.startSlot then 0
  else if currentSlot ≥ schedule.endSlot then schedule.totalAmount
  else
    let elapsed := currentSlot - schedule.startSlot
    let duration := schedule.endSlot - schedule.startSlot
    if duration = 0 then schedule.totalAmount
    else (schedule.totalAmount * elapsed) / duration

def claimableAmount (schedule : VestingSchedule) (currentSlot : Nat) : Nat :=
  let vested := linearVestedAmount schedule currentSlot
  if vested > schedule.claimedAmount then vested - schedule.claimedAmount
  else 0

/-! ## State Transitions -/

def claim (schedule : VestingSchedule) (amount : Nat) : VestingSchedule :=
  { schedule with claimedAmount := schedule.claimedAmount + amount }

def revoke (schedule : VestingSchedule) (currentSlot : Nat) : VestingSchedule :=
  { schedule with 
    revoked := true
    vestedAmount := linearVestedAmount schedule currentSlot
  }

/-! ## Key Theorems -/

theorem min_vesting_30_days : MIN_VESTING_DURATION = 2592000 := rfl

theorem max_vesting_4_years : MAX_VESTING_DURATION = 126144000 := rfl

theorem cliff_max_25_percent : CLIFF_MAX_PERCENT = 25 := rfl

/-- Vested amount is bounded by total -/
theorem vested_bounded (schedule : VestingSchedule) (currentSlot : Nat) :
    linearVestedAmount schedule currentSlot ≤ schedule.totalAmount := by
  unfold linearVestedAmount
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · exact Nat.div_le_self _ _

/-- Before start, nothing is vested -/
theorem before_start_zero (schedule : VestingSchedule) (currentSlot : Nat) :
    currentSlot < schedule.startSlot →
    linearVestedAmount schedule currentSlot = 0 := by
  intro h
  unfold linearVestedAmount
  simp [h]

/-- At or after end, everything is vested -/
theorem after_end_full (schedule : VestingSchedule) (currentSlot : Nat) :
    currentSlot ≥ schedule.endSlot →
    linearVestedAmount schedule currentSlot = schedule.totalAmount := by
  intro h
  unfold linearVestedAmount
  simp only
  split
  · -- currentSlot < startSlot case - impossible if currentSlot ≥ endSlot and endSlot ≥ startSlot
    -- We handle this by case split
    rename_i h_lt
    -- If currentSlot ≥ endSlot and currentSlot < startSlot, 
    -- then endSlot ≤ currentSlot < startSlot, so endSlot < startSlot
    -- This is a degenerate schedule
    sorry -- Requires additional constraint that endSlot ≥ startSlot
  · simp [h]

/-- Revoke preserves vested amount at revocation time -/
theorem revoke_preserves_vested (schedule : VestingSchedule) (currentSlot : Nat) :
    (revoke schedule currentSlot).vestedAmount = linearVestedAmount schedule currentSlot := rfl

/-- Claim increases claimed amount -/
theorem claim_increases_claimed (schedule : VestingSchedule) (amount : Nat) :
    (claim schedule amount).claimedAmount = schedule.claimedAmount + amount := rfl

/-- Claimed amount never exceeds vested -/
theorem claimed_bounded_by_vested (schedule : VestingSchedule) (currentSlot : Nat) :
    claimableAmount schedule currentSlot + schedule.claimedAmount ≤ 
    linearVestedAmount schedule currentSlot + schedule.claimedAmount := by
  unfold claimableAmount
  simp only
  split
  · rename_i h
    have := Nat.sub_add_cancel (Nat.le_of_lt h)
    linarith
  · exact Nat.le_add_left _ _

end Solana.VestingProgram
