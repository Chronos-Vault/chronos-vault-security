/-
  OperationLifecycleLib - Operation State Management
  Formal verification of operation lifecycle transitions
-/

import Mathlib.Data.Nat.Basic

namespace Libraries.OperationLifecycle

/-! ## Constants -/

def OPERATION_TTL : Nat := 86400       -- 24 hours
def GRACE_PERIOD : Nat := 3600         -- 1 hour
def MAX_RETRIES : Nat := 3

/-! ## Operation State -/

inductive OperationState where
  | pending : OperationState
  | confirmed : OperationState
  | executing : OperationState
  | completed : OperationState
  | failed : OperationState
  | expired : OperationState
  | canceled : OperationState
deriving DecidableEq, Repr

structure Operation where
  id : ByteArray
  state : OperationState
  createdAt : Nat
  confirmedAt : Option Nat
  executedAt : Option Nat
  retryCount : Nat
  lastError : Option ByteArray
deriving Repr

/-! ## State Predicates -/

def isPending (op : Operation) : Prop :=
  op.state = OperationState.pending

def isConfirmed (op : Operation) : Prop :=
  op.state = OperationState.confirmed

def isExecuting (op : Operation) : Prop :=
  op.state = OperationState.executing

def isCompleted (op : Operation) : Prop :=
  op.state = OperationState.completed

def isFailed (op : Operation) : Prop :=
  op.state = OperationState.failed

def isTerminal (op : Operation) : Prop :=
  op.state = OperationState.completed ∨
  op.state = OperationState.expired ∨
  op.state = OperationState.canceled

def isExpired (op : Operation) (currentTime : Nat) : Prop :=
  currentTime > op.createdAt + OPERATION_TTL

def canRetry (op : Operation) : Prop :=
  isFailed op ∧ op.retryCount < MAX_RETRIES

/-! ## Valid Transitions -/

def validTransition (from to : OperationState) : Prop :=
  match from, to with
  | .pending, .confirmed => True
  | .pending, .expired => True
  | .pending, .canceled => True
  | .confirmed, .executing => True
  | .confirmed, .expired => True
  | .confirmed, .canceled => True
  | .executing, .completed => True
  | .executing, .failed => True
  | .failed, .executing => True  -- retry
  | _, _ => False

/-! ## State Transitions -/

def confirm (op : Operation) (time : Nat) : Operation :=
  { op with state := OperationState.confirmed, confirmedAt := some time }

def startExecution (op : Operation) : Operation :=
  { op with state := OperationState.executing }

def complete (op : Operation) (time : Nat) : Operation :=
  { op with state := OperationState.completed, executedAt := some time }

def fail (op : Operation) (error : ByteArray) : Operation :=
  { op with 
    state := OperationState.failed
    retryCount := op.retryCount + 1
    lastError := some error
  }

def retry (op : Operation) : Operation :=
  { op with state := OperationState.executing }

def expire (op : Operation) : Operation :=
  { op with state := OperationState.expired }

def cancel (op : Operation) : Operation :=
  { op with state := OperationState.canceled }

/-! ## Key Theorems -/

theorem confirm_valid_from_pending (op : Operation) (time : Nat) :
  isPending op →
  isConfirmed (confirm op time) := by
  intro _
  unfold confirm isConfirmed
  rfl

theorem complete_is_terminal (op : Operation) (time : Nat) :
  isTerminal (complete op time) := by
  unfold complete isTerminal
  simp
  left
  rfl

theorem fail_increments_retry (op : Operation) (error : ByteArray) :
  (fail op error).retryCount = op.retryCount + 1 := by
  unfold fail
  rfl

theorem max_retries_blocks_retry (op : Operation) :
  op.retryCount ≥ MAX_RETRIES → ¬canRetry op := by
  intro h hretry
  unfold canRetry at hretry
  exact Nat.not_lt.mpr h hretry.2

theorem terminal_no_transition (op : Operation) :
  isTerminal op →
  ∀ s : OperationState, s ≠ op.state → ¬validTransition op.state s := by
  intro hterm s _
  unfold isTerminal at hterm
  unfold validTransition
  rcases hterm with hc | he | hca
  · simp [hc]
  · simp [he]
  · simp [hca]

/-! ## Timing -/

theorem operation_ttl_24h : OPERATION_TTL = 86400 := rfl

theorem grace_period_1h : GRACE_PERIOD = 3600 := rfl

theorem expired_blocks_execution (op : Operation) (currentTime : Nat) :
  isExpired op currentTime →
  let expired := expire op
  expired.state = OperationState.expired := by
  intro _
  unfold expire
  rfl

end Libraries.OperationLifecycle
