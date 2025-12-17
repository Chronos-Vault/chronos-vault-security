/-
  Trinity Protocol - Consensus Module
  Core 2-of-3 Byzantine Fault Tolerant consensus proofs
  
  This module provides the mathematical foundations for
  the Trinity Protocol's multi-chain consensus mechanism.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

namespace Trinity.Consensus

/-! ## Constants -/

def TOTAL_VALIDATORS : Nat := 3
def CONSENSUS_THRESHOLD : Nat := 2
def MAX_FAULTY : Nat := 1

/-! ## Chain Confirmation State -/

structure ConsensusState where
  arbitrumConfirmed : Bool
  solanaConfirmed : Bool
  tonConfirmed : Bool
deriving Repr, DecidableEq

/-! ## Counting Functions -/

def confirmationCount (s : ConsensusState) : Nat :=
  (if s.arbitrumConfirmed then 1 else 0) +
  (if s.solanaConfirmed then 1 else 0) +
  (if s.tonConfirmed then 1 else 0)

def hasConsensus (s : ConsensusState) : Prop :=
  confirmationCount s ≥ CONSENSUS_THRESHOLD

/-! ## Pair Predicates -/

def arbitrumSolanaPair (s : ConsensusState) : Prop :=
  s.arbitrumConfirmed ∧ s.solanaConfirmed

def arbitrumTonPair (s : ConsensusState) : Prop :=
  s.arbitrumConfirmed ∧ s.tonConfirmed

def solanaTonPair (s : ConsensusState) : Prop :=
  s.solanaConfirmed ∧ s.tonConfirmed

def validConsensusPair (s : ConsensusState) : Prop :=
  arbitrumSolanaPair s ∨ arbitrumTonPair s ∨ solanaTonPair s

/-! ## Core Safety Theorem -/

theorem consensus_implies_valid_pair (s : ConsensusState) :
  hasConsensus s → validConsensusPair s := by
  intro h
  unfold hasConsensus CONSENSUS_THRESHOLD at h
  unfold validConsensusPair arbitrumSolanaPair arbitrumTonPair solanaTonPair
  unfold confirmationCount at h
  cases s.arbitrumConfirmed <;> cases s.solanaConfirmed <;> cases s.tonConfirmed <;>
    simp only [ite_true, ite_false, Nat.add_zero, zero_add] at h
  all_goals tauto

theorem valid_pair_implies_consensus (s : ConsensusState) :
  validConsensusPair s → hasConsensus s := by
  intro h
  unfold validConsensusPair arbitrumSolanaPair arbitrumTonPair solanaTonPair at h
  unfold hasConsensus CONSENSUS_THRESHOLD confirmationCount
  cases s.arbitrumConfirmed <;> cases s.solanaConfirmed <;> cases s.tonConfirmed <;>
    simp only [ite_true, ite_false, Nat.add_zero, zero_add, and_true, and_false] at h ⊢
  all_goals (try tauto)

/-! ## Byzantine Fault Tolerance -/

def byzantineSafe (faultyCount : Nat) : Prop :=
  faultyCount ≤ MAX_FAULTY

theorem bft_guarantees_honest_majority :
  ∀ faulty : Nat, byzantineSafe faulty → 
  TOTAL_VALIDATORS - faulty ≥ CONSENSUS_THRESHOLD := by
  intro faulty h
  unfold byzantineSafe MAX_FAULTY at h
  unfold TOTAL_VALIDATORS CONSENSUS_THRESHOLD
  omega

theorem single_fault_tolerated :
  byzantineSafe 1 := by
  unfold byzantineSafe MAX_FAULTY
  norm_num

theorem double_fault_breaks_consensus :
  ¬byzantineSafe 2 := by
  unfold byzantineSafe MAX_FAULTY
  norm_num

/-! ## Liveness Guarantee -/

theorem no_single_chain_veto (s : ConsensusState) :
  (s.solanaConfirmed ∧ s.tonConfirmed) → hasConsensus s := by
  intro h
  unfold hasConsensus CONSENSUS_THRESHOLD confirmationCount
  obtain ⟨hs, ht⟩ := h
  simp [hs, ht]

theorem arbitrum_not_required (s : ConsensusState) :
  s.arbitrumConfirmed = false → s.solanaConfirmed → s.tonConfirmed → 
  hasConsensus s := by
  intro harb hsol hton
  unfold hasConsensus CONSENSUS_THRESHOLD confirmationCount
  simp [harb, hsol, hton]

theorem any_two_chains_sufficient (a b c : Bool) :
  (a && b) || (a && c) || (b && c) = true →
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) ≥ 2 := by
  intro h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  cases a <;> cases b <;> cases c <;> 
    simp only [ite_true, ite_false, Nat.add_zero, zero_add]
  all_goals (try omega)
  all_goals (simp at h)

/-! ## Confirmation Monotonicity -/

def confirmsArbitrum (before after : ConsensusState) : Prop :=
  before.arbitrumConfirmed = false ∧ after.arbitrumConfirmed = true ∧
  before.solanaConfirmed = after.solanaConfirmed ∧
  before.tonConfirmed = after.tonConfirmed

theorem confirmation_increases_count (before after : ConsensusState) :
  confirmsArbitrum before after →
  confirmationCount after = confirmationCount before + 1 := by
  intro h
  unfold confirmsArbitrum at h
  obtain ⟨harb_f, harb_t, hsol, hton⟩ := h
  unfold confirmationCount
  simp [harb_f, harb_t, hsol, hton]

theorem consensus_preserved (before after : ConsensusState) :
  hasConsensus before →
  confirmationCount after ≥ confirmationCount before →
  hasConsensus after := by
  intro hcon hge
  unfold hasConsensus at hcon ⊢
  exact Nat.le_trans hcon hge

/-! ## Quorum Mathematics -/

theorem threshold_is_strict_majority :
  CONSENSUS_THRESHOLD * 2 > TOTAL_VALIDATORS := by
  unfold CONSENSUS_THRESHOLD TOTAL_VALIDATORS
  norm_num

theorem threshold_minimal :
  ∀ t : Nat, t * 2 > TOTAL_VALIDATORS → t ≥ CONSENSUS_THRESHOLD := by
  intro t h
  unfold TOTAL_VALIDATORS at h
  unfold CONSENSUS_THRESHOLD
  omega

end Trinity.Consensus
