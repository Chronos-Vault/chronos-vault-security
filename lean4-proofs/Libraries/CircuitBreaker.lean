/-
  CircuitBreakerLib - Emergency Circuit Breaker
  Formal verification of pause/unpause mechanics
-/

import Mathlib.Data.Nat.Basic

namespace Libraries.CircuitBreaker

/-! ## Constants -/

def COOLDOWN_PERIOD : Nat := 3600      -- 1 hour
def MAX_TRIGGERS_PER_DAY : Nat := 3
def AUTO_UNPAUSE_DELAY : Nat := 86400  -- 24 hours

/-! ## Circuit State -/

inductive CircuitState where
  | active : CircuitState
  | paused : CircuitState
  | cooldown : CircuitState
deriving DecidableEq, Repr

structure CircuitBreaker where
  state : CircuitState
  pausedAt : Option Nat
  triggerCount : Nat
  lastTriggerTime : Nat
  autoUnpauseTime : Option Nat
deriving Repr

/-! ## Predicates -/

def isPaused (cb : CircuitBreaker) : Prop :=
  cb.state = CircuitState.paused

def isActive (cb : CircuitBreaker) : Prop :=
  cb.state = CircuitState.active

def inCooldown (cb : CircuitBreaker) (currentTime : Nat) : Prop :=
  cb.state = CircuitState.cooldown ∧
  currentTime < cb.lastTriggerTime + COOLDOWN_PERIOD

def canTrigger (cb : CircuitBreaker) (currentTime : Nat) : Prop :=
  isActive cb ∧ 
  cb.triggerCount < MAX_TRIGGERS_PER_DAY ∧
  ¬inCooldown cb currentTime

def canAutoUnpause (cb : CircuitBreaker) (currentTime : Nat) : Prop :=
  isPaused cb ∧
  match cb.autoUnpauseTime with
  | some t => currentTime ≥ t
  | none => False

/-! ## State Transitions -/

def pause (cb : CircuitBreaker) (currentTime : Nat) : CircuitBreaker :=
  { cb with
    state := CircuitState.paused
    pausedAt := some currentTime
    triggerCount := cb.triggerCount + 1
    lastTriggerTime := currentTime
    autoUnpauseTime := some (currentTime + AUTO_UNPAUSE_DELAY)
  }

def unpause (cb : CircuitBreaker) : CircuitBreaker :=
  { cb with
    state := CircuitState.active
    pausedAt := none
    autoUnpauseTime := none
  }

def enterCooldown (cb : CircuitBreaker) (currentTime : Nat) : CircuitBreaker :=
  { cb with
    state := CircuitState.cooldown
    lastTriggerTime := currentTime
  }

def resetDailyCount (cb : CircuitBreaker) : CircuitBreaker :=
  { cb with triggerCount := 0 }

/-! ## Key Theorems -/

theorem pause_sets_state (cb : CircuitBreaker) (t : Nat) :
  isPaused (pause cb t) := by
  unfold pause isPaused
  rfl

theorem unpause_activates (cb : CircuitBreaker) :
  isActive (unpause cb) := by
  unfold unpause isActive
  rfl

theorem pause_increments_trigger_count (cb : CircuitBreaker) (t : Nat) :
  (pause cb t).triggerCount = cb.triggerCount + 1 := by
  unfold pause
  rfl

theorem max_triggers_blocks_pause (cb : CircuitBreaker) (currentTime : Nat) :
  cb.triggerCount ≥ MAX_TRIGGERS_PER_DAY →
  ¬canTrigger cb currentTime := by
  intro h htrig
  unfold canTrigger at htrig
  exact Nat.not_lt.mpr h htrig.2.1

/-! ## Auto-Unpause -/

theorem auto_unpause_after_24h : AUTO_UNPAUSE_DELAY = 86400 := rfl

theorem auto_unpause_time_set (cb : CircuitBreaker) (t : Nat) :
  (pause cb t).autoUnpauseTime = some (t + AUTO_UNPAUSE_DELAY) := by
  unfold pause
  rfl

theorem auto_unpause_eventual (cb : CircuitBreaker) (pauseTime : Nat) :
  let paused := pause cb pauseTime
  canAutoUnpause paused (pauseTime + AUTO_UNPAUSE_DELAY) := by
  unfold pause canAutoUnpause isPaused
  simp

/-! ## Cooldown -/

theorem cooldown_period_1h : COOLDOWN_PERIOD = 3600 := rfl

theorem cooldown_blocks_trigger (cb : CircuitBreaker) (currentTime : Nat) :
  inCooldown cb currentTime → ¬canTrigger cb currentTime := by
  intro hcool htrig
  unfold canTrigger at htrig
  unfold inCooldown at hcool
  simp [hcool.1] at htrig

end Libraries.CircuitBreaker
