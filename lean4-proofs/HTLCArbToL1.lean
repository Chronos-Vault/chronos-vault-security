/-
  HTLCArbToL1 - Arbitrum to L1 HTLC Bridge
  Formal verification of L2 to L1 atomic swaps
  
  Deployed: 0xaDDAC5670941416063551c996e169b0fa569B8e1 (Arbitrum Sepolia)
-/

import Mathlib.Data.Nat.Basic

namespace HTLCArbToL1

/-! ## Constants -/

def MIN_TIMELOCK : Nat := 3600         -- 1 hour minimum
def MAX_TIMELOCK : Nat := 604800       -- 7 days maximum
def L1_FINALITY_BLOCKS : Nat := 12
def ARB_CHALLENGE_PERIOD : Nat := 604800  -- 7 days

/-! ## Swap State -/

inductive SwapDirection where
  | arbToL1 : SwapDirection
  | l1ToArb : SwapDirection
deriving DecidableEq, Repr

structure L2Swap where
  swapId : ByteArray
  sender : ByteArray
  recipient : ByteArray
  amount : Nat
  hashlock : ByteArray
  timelock : Nat
  direction : SwapDirection
  l1TxHash : Option ByteArray
  claimed : Bool
  refunded : Bool
  createdAt : Nat
deriving Repr

/-! ## Predicates -/

def isActive (swap : L2Swap) (currentTime : Nat) : Prop :=
  ¬swap.claimed ∧ ¬swap.refunded ∧ currentTime ≤ swap.timelock

def isExpired (swap : L2Swap) (currentTime : Nat) : Prop :=
  currentTime > swap.timelock

def canClaim (swap : L2Swap) (currentTime : Nat) : Prop :=
  isActive swap currentTime

def canRefund (swap : L2Swap) (currentTime : Nat) : Prop :=
  ¬swap.claimed ∧ ¬swap.refunded ∧ isExpired swap currentTime

def isFinalized (swap : L2Swap) : Prop :=
  swap.claimed ∨ swap.refunded

def validTimelock (createdAt timelock : Nat) : Prop :=
  let duration := timelock - createdAt
  duration ≥ MIN_TIMELOCK ∧ duration ≤ MAX_TIMELOCK

/-! ## L1 Finality -/

def l1Finalized (swap : L2Swap) : Prop :=
  swap.l1TxHash.isSome

def waitingForL1 (swap : L2Swap) : Prop :=
  swap.direction = SwapDirection.arbToL1 ∧ swap.l1TxHash.isNone

/-! ## State Transitions -/

def claim (swap : L2Swap) : L2Swap :=
  { swap with claimed := true }

def refund (swap : L2Swap) : L2Swap :=
  { swap with refunded := true }

def setL1TxHash (swap : L2Swap) (txHash : ByteArray) : L2Swap :=
  { swap with l1TxHash := some txHash }

/-! ## Key Theorems -/

theorem claim_finalizes (swap : L2Swap) :
  isFinalized (claim swap) := by
  unfold claim isFinalized
  simp
  left
  rfl

theorem refund_finalizes (swap : L2Swap) :
  isFinalized (refund swap) := by
  unfold refund isFinalized
  simp
  right
  rfl

theorem mutual_exclusion (swap : L2Swap) (currentTime : Nat) :
  isActive swap currentTime → ¬isExpired swap currentTime := by
  intro hact hexp
  unfold isActive at hact
  unfold isExpired at hexp
  exact Nat.not_lt.mpr hact.2.2 hexp

theorem expired_enables_refund (swap : L2Swap) (currentTime : Nat) :
  ¬swap.claimed → ¬swap.refunded → isExpired swap currentTime →
  canRefund swap currentTime := by
  intro hc hr hexp
  unfold canRefund
  exact ⟨hc, hr, hexp⟩

/-! ## Timelock Bounds -/

theorem min_timelock_1_hour : MIN_TIMELOCK = 3600 := rfl

theorem max_timelock_7_days : MAX_TIMELOCK = 604800 := rfl

theorem timelock_provides_window (createdAt timelock : Nat) :
  validTimelock createdAt timelock →
  timelock ≥ createdAt + MIN_TIMELOCK := by
  intro h
  unfold validTimelock at h
  omega

theorem timelock_bounded (createdAt timelock : Nat) :
  validTimelock createdAt timelock →
  timelock ≤ createdAt + MAX_TIMELOCK := by
  intro h
  unfold validTimelock at h
  omega

/-! ## L1 Integration -/

theorem l1_hash_recorded (swap : L2Swap) (txHash : ByteArray) :
  (setL1TxHash swap txHash).l1TxHash = some txHash := by
  unfold setL1TxHash
  rfl

theorem arb_to_l1_requires_l1_finality (swap : L2Swap) :
  swap.direction = SwapDirection.arbToL1 →
  swap.l1TxHash.isNone →
  waitingForL1 swap := by
  intro hdir hnone
  unfold waitingForL1
  exact ⟨hdir, hnone⟩

/-! ## Amount Conservation -/

theorem claim_preserves_amount (swap : L2Swap) :
  (claim swap).amount = swap.amount := by
  unfold claim
  rfl

theorem refund_preserves_amount (swap : L2Swap) :
  (refund swap).amount = swap.amount := by
  unfold refund
  rfl

end HTLCArbToL1
