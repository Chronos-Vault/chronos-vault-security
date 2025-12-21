/-
  Trinity Protocol - Vote Trace Module (Complete Formal Verification)
  Rigorous invariant modeling for validator vote tracking
  
  This module models the on-chain vote submission and tracking
  mechanism used by the Trinity 2-of-3 consensus system.
  
  All theorems proven - ZERO `sorry` statements
  Mathlib-free for portability and fast compilation
-/

namespace Trinity.VoteTrace

/-! =====================================================
    SECTION 1: CHAIN IDENTIFIERS
    ===================================================== -/

inductive ChainId where
  | arbitrum : ChainId
  | solana : ChainId
  | ton : ChainId
deriving DecidableEq, Repr, Inhabited

def ChainId.toNat : ChainId → Nat
  | .arbitrum => 1
  | .solana => 2
  | .ton => 3

theorem chainId_toNat_injective (c1 c2 : ChainId) :
    c1.toNat = c2.toNat → c1 = c2 := by
  intro h
  cases c1 <;> cases c2 <;> simp [ChainId.toNat] at h <;> rfl

theorem chainId_toNat_bounded (c : ChainId) :
    1 ≤ c.toNat ∧ c.toNat ≤ 3 := by
  cases c <;> simp [ChainId.toNat]

theorem chainId_exactly_three :
    ∀ c : ChainId, c = .arbitrum ∨ c = .solana ∨ c = .ton := by
  intro c
  cases c
  · left; rfl
  · right; left; rfl
  · right; right; rfl

theorem chainId_distinct_arb_sol : ChainId.arbitrum ≠ ChainId.solana := by decide
theorem chainId_distinct_arb_ton : ChainId.arbitrum ≠ ChainId.ton := by decide
theorem chainId_distinct_sol_ton : ChainId.solana ≠ ChainId.ton := by decide

/-! =====================================================
    SECTION 2: VOTE RECORD STRUCTURE
    ===================================================== -/

structure Vote where
  chainId : ChainId
  validator : Nat
  timestamp : Nat
  operationId : Nat
deriving Repr, DecidableEq

structure VoteTrace where
  votes : List Vote
  operationId : Nat
deriving Repr

/-! =====================================================
    SECTION 3: VOTE COUNTING
    ===================================================== -/

def voteCount (trace : VoteTrace) : Nat :=
  trace.votes.length

def chainHasVote (trace : VoteTrace) (chain : ChainId) : Bool :=
  trace.votes.any (·.chainId == chain)

def countVotesForChain (trace : VoteTrace) (chain : ChainId) : Nat :=
  (trace.votes.filter (·.chainId == chain)).length

def totalDistinctChains (trace : VoteTrace) : Nat :=
  let hasArb := trace.votes.any (·.chainId == .arbitrum)
  let hasSol := trace.votes.any (·.chainId == .solana)
  let hasTon := trace.votes.any (·.chainId == .ton)
  (if hasArb then 1 else 0) + (if hasSol then 1 else 0) + (if hasTon then 1 else 0)

/-! =====================================================
    SECTION 4: VOTE OPERATIONS
    ===================================================== -/

def addVote (trace : VoteTrace) (vote : Vote) : VoteTrace :=
  { trace with votes := vote :: trace.votes }

def emptyTrace (opId : Nat) : VoteTrace :=
  { votes := [], operationId := opId }

/-! =====================================================
    SECTION 5: UNIQUENESS PREDICATE
    ===================================================== -/

def uniqueChainVotes (trace : VoteTrace) : Prop :=
  ∀ v1 v2 : Vote, v1 ∈ trace.votes → v2 ∈ trace.votes →
    v1.chainId = v2.chainId → v1 = v2

def noDoubleVoting (trace : VoteTrace) : Prop :=
  ∀ c : ChainId, countVotesForChain trace c ≤ 1

def votesNodup (trace : VoteTrace) : Prop :=
  trace.votes.Nodup

/-! Helper: NoDup invariant combined with chain uniqueness -/
structure WellFormedTrace where
  trace : VoteTrace
  nodup : trace.votes.Nodup
  chainUnique : uniqueChainVotes trace

/-! Filter of a Nodup list is Nodup -/
theorem filter_nodup_of_nodup {α : Type} (p : α → Bool) (l : List α) :
    l.Nodup → (l.filter p).Nodup := by
  intro hnd
  exact List.Nodup.sublist (List.filter_sublist l) hnd

/-! Core lemma: under uniqueness + nodup, filtered list has ≤ 1 elements -/
theorem filter_chain_le_one (trace : VoteTrace) (c : ChainId) :
    trace.votes.Nodup →
    uniqueChainVotes trace →
    (trace.votes.filter (·.chainId == c)).length ≤ 1 := by
  intro h_nodup h_unique
  match hf : trace.votes.filter (·.chainId == c) with
  | [] => simp [hf]
  | [_] => simp [hf]
  | v1 :: v2 :: rest =>
    have hv1_in : v1 ∈ trace.votes.filter (·.chainId == c) := by rw [hf]; simp
    have hv2_in : v2 ∈ trace.votes.filter (·.chainId == c) := by rw [hf]; simp
    have ⟨hv1_mem, hv1_chain⟩ := List.mem_filter.mp hv1_in
    have ⟨hv2_mem, hv2_chain⟩ := List.mem_filter.mp hv2_in
    simp only [beq_iff_eq] at hv1_chain hv2_chain
    have heq_chain : v1.chainId = v2.chainId := hv1_chain.trans hv2_chain.symm
    have heq : v1 = v2 := h_unique v1 v2 hv1_mem hv2_mem heq_chain
    rw [heq] at hf
    have hfilt_nodup : (trace.votes.filter (·.chainId == c)).Nodup :=
      filter_nodup_of_nodup _ trace.votes h_nodup
    rw [hf] at hfilt_nodup
    have hv2_in_rest : v2 ∈ v2 :: rest := List.mem_cons_self v2 rest
    have := List.nodup_cons.mp hfilt_nodup
    exact absurd hv2_in_rest this.1

/-! Main theorem: uniqueness + nodup implies no double voting -/
theorem uniqueness_nodup_implies_no_double_voting (trace : VoteTrace) :
    trace.votes.Nodup →
    uniqueChainVotes trace →
    noDoubleVoting trace := by
  intro h_nodup h_unique
  unfold noDoubleVoting countVotesForChain
  intro c
  exact filter_chain_le_one trace c h_nodup h_unique

/-! Well-formed trace guarantees no double voting -/
theorem wellformed_no_double_voting (wt : WellFormedTrace) :
    noDoubleVoting wt.trace :=
  uniqueness_nodup_implies_no_double_voting wt.trace wt.nodup wt.chainUnique

/-! =====================================================
    SECTION 5a: UNIQUENESS PRESERVATION
    ===================================================== -/

theorem add_vote_preserves_uniqueness (trace : VoteTrace) (vote : Vote) :
    uniqueChainVotes trace →
    chainHasVote trace vote.chainId = false →
    uniqueChainVotes (addVote trace vote) := by
  intro h_unique h_new
  unfold uniqueChainVotes addVote at *
  intro v1 v2 hv1 hv2 hchain
  simp only [List.mem_cons] at hv1 hv2
  cases hv1 with
  | inl h1 =>
    cases hv2 with
    | inl h2 => rw [h1, h2]
    | inr h2 =>
      rw [h1] at hchain
      unfold chainHasVote at h_new
      have hany : trace.votes.any (·.chainId == vote.chainId) = true := by
        simp only [List.any_eq_true, beq_iff_eq]
        exact ⟨v2, h2, hchain.symm⟩
      simp [hany] at h_new
  | inr h1 =>
    cases hv2 with
    | inl h2 =>
      rw [h2] at hchain
      unfold chainHasVote at h_new
      have hany : trace.votes.any (·.chainId == vote.chainId) = true := by
        simp only [List.any_eq_true, beq_iff_eq]
        exact ⟨v1, h1, hchain⟩
      simp [hany] at h_new
    | inr h2 => exact h_unique v1 v2 h1 h2 hchain

theorem uniqueness_blocks_double_vote (trace : VoteTrace) (vote : Vote) :
    uniqueChainVotes trace →
    chainHasVote trace vote.chainId = true →
    ∃ v ∈ trace.votes, v.chainId = vote.chainId := by
  intro _ h_has
  unfold chainHasVote at h_has
  simp only [List.any_eq_true, beq_iff_eq] at h_has
  exact h_has

theorem double_vote_contradicts_uniqueness (trace : VoteTrace) (v1 v2 : Vote) :
    uniqueChainVotes trace →
    v1 ∈ trace.votes →
    v2 ∈ trace.votes →
    v1.chainId = v2.chainId →
    v1 ≠ v2 →
    False := by
  intro h_unique hv1 hv2 hchain hne
  have heq := h_unique v1 v2 hv1 hv2 hchain
  exact hne heq

theorem empty_no_double_voting (opId : Nat) :
    noDoubleVoting (emptyTrace opId) := by
  unfold noDoubleVoting countVotesForChain emptyTrace
  intro c
  simp [List.filter]

/-! =====================================================
    SECTION 6: EMPTY TRACE THEOREMS
    ===================================================== -/

theorem empty_trace_count (opId : Nat) :
    voteCount (emptyTrace opId) = 0 := rfl

theorem empty_trace_no_votes (opId : Nat) (chain : ChainId) :
    chainHasVote (emptyTrace opId) chain = false := by
  unfold emptyTrace chainHasVote
  simp [List.any]

theorem empty_trace_unique (opId : Nat) :
    uniqueChainVotes (emptyTrace opId) := by
  unfold uniqueChainVotes emptyTrace
  intro v1 v2 hv1 _ _
  exact absurd hv1 (List.not_mem_nil v1)

theorem empty_trace_zero_distinct (opId : Nat) :
    totalDistinctChains (emptyTrace opId) = 0 := by
  unfold emptyTrace totalDistinctChains
  simp [List.any]

/-! =====================================================
    SECTION 7: ADD VOTE THEOREMS
    ===================================================== -/

theorem add_vote_count (trace : VoteTrace) (vote : Vote) :
    voteCount (addVote trace vote) = voteCount trace + 1 := by
  unfold addVote voteCount
  simp [List.length_cons]

theorem add_vote_preserves_operation_id (trace : VoteTrace) (vote : Vote) :
    (addVote trace vote).operationId = trace.operationId := rfl

theorem added_vote_present (trace : VoteTrace) (vote : Vote) :
    chainHasVote (addVote trace vote) vote.chainId = true := by
  unfold addVote chainHasVote
  simp [List.any_cons]

theorem add_preserves_existing_votes (trace : VoteTrace) (vote : Vote) (chain : ChainId) :
    chainHasVote trace chain = true → chainHasVote (addVote trace vote) chain = true := by
  intro h
  unfold addVote chainHasVote at *
  simp only [List.any_cons, Bool.or_eq_true]
  right
  exact h

/-! =====================================================
    SECTION 8: VOTE MONOTONICITY
    ===================================================== -/

theorem votes_monotonic (trace : VoteTrace) (vote : Vote) :
    voteCount trace ≤ voteCount (addVote trace vote) := by
  rw [add_vote_count]
  exact Nat.le_add_right _ 1

/-! =====================================================
    SECTION 9: CONSENSUS DETECTION
    ===================================================== -/

def CONSENSUS_THRESHOLD : Nat := 2
def TOTAL_CHAINS : Nat := 3

def hasConsensus (trace : VoteTrace) : Prop :=
  totalDistinctChains trace ≥ CONSENSUS_THRESHOLD

theorem consensus_threshold_correct : CONSENSUS_THRESHOLD = 2 := rfl
theorem total_chains_correct : TOTAL_CHAINS = 3 := rfl

theorem zero_votes_no_consensus (opId : Nat) :
    ¬hasConsensus (emptyTrace opId) := by
  unfold hasConsensus CONSENSUS_THRESHOLD
  rw [empty_trace_zero_distinct]
  omega

theorem three_votes_implies_all_chains (trace : VoteTrace) :
    totalDistinctChains trace = 3 →
    chainHasVote trace .arbitrum = true ∧
    chainHasVote trace .solana = true ∧
    chainHasVote trace .ton = true := by
  unfold totalDistinctChains chainHasVote
  intro h
  cases harb : trace.votes.any (·.chainId == .arbitrum)
  <;> cases hsol : trace.votes.any (·.chainId == .solana)
  <;> cases hton : trace.votes.any (·.chainId == .ton)
  <;> simp_all

theorem two_distinct_implies_consensus (trace : VoteTrace) :
    totalDistinctChains trace ≥ 2 → hasConsensus trace := by
  intro h
  unfold hasConsensus CONSENSUS_THRESHOLD
  exact h

/-! =====================================================
    SECTION 10: DISTINCT CHAIN COUNT BOUNDS
    ===================================================== -/

theorem distinct_chains_bounded (trace : VoteTrace) :
    totalDistinctChains trace ≤ 3 := by
  unfold totalDistinctChains
  cases trace.votes.any (·.chainId == .arbitrum)
  <;> cases trace.votes.any (·.chainId == .solana)
  <;> cases trace.votes.any (·.chainId == .ton)
  <;> simp

theorem distinct_chains_nonneg (trace : VoteTrace) :
    0 ≤ totalDistinctChains trace := Nat.zero_le _

/-! =====================================================
    SECTION 11: CONSENSUS FROM TWO CHAINS
    ===================================================== -/

theorem consensus_arb_sol (trace : VoteTrace) :
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .solana = true →
    hasConsensus trace := by
  intro harb hsol
  unfold hasConsensus CONSENSUS_THRESHOLD totalDistinctChains
  simp only [chainHasVote] at harb hsol
  simp [harb, hsol]

theorem consensus_arb_ton (trace : VoteTrace) :
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro harb hton
  unfold hasConsensus CONSENSUS_THRESHOLD totalDistinctChains
  simp only [chainHasVote] at harb hton
  simp [harb, hton]

theorem consensus_sol_ton (trace : VoteTrace) :
    chainHasVote trace .solana = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro hsol hton
  unfold hasConsensus CONSENSUS_THRESHOLD totalDistinctChains
  simp only [chainHasVote] at hsol hton
  simp [hsol, hton]

/-! =====================================================
    SECTION 12: CONSENSUS STABILITY
    ===================================================== -/

theorem consensus_preserved_stronger (trace1 trace2 : VoteTrace) :
    hasConsensus trace1 →
    totalDistinctChains trace2 ≥ totalDistinctChains trace1 →
    hasConsensus trace2 := by
  intro h1 h2
  unfold hasConsensus at *
  exact Nat.le_trans h1 h2

/-! =====================================================
    SECTION 13: VOTE FLAG EQUIVALENCE (On-Chain Bitmap)
    ===================================================== -/

structure VoteFlags where
  arbitrum : Bool
  solana : Bool
  ton : Bool
deriving Repr, DecidableEq

def voteFlagsFromTrace (trace : VoteTrace) : VoteFlags :=
  { arbitrum := chainHasVote trace .arbitrum
  , solana := chainHasVote trace .solana
  , ton := chainHasVote trace .ton }

def flagCount (flags : VoteFlags) : Nat :=
  (if flags.arbitrum then 1 else 0) +
  (if flags.solana then 1 else 0) +
  (if flags.ton then 1 else 0)

theorem vote_count_matches_flags (trace : VoteTrace) :
    totalDistinctChains trace = flagCount (voteFlagsFromTrace trace) := by
  unfold totalDistinctChains voteFlagsFromTrace flagCount chainHasVote
  rfl

theorem flags_consensus_equivalence (trace : VoteTrace) :
    hasConsensus trace ↔ flagCount (voteFlagsFromTrace trace) ≥ 2 := by
  unfold hasConsensus CONSENSUS_THRESHOLD
  rw [vote_count_matches_flags]

theorem flag_arb_sol_consensus (f : VoteFlags) :
    f.arbitrum = true → f.solana = true → flagCount f ≥ 2 := by
  intro harb hsol
  unfold flagCount
  simp [harb, hsol]

theorem flag_arb_ton_consensus (f : VoteFlags) :
    f.arbitrum = true → f.ton = true → flagCount f ≥ 2 := by
  intro harb hton
  unfold flagCount
  simp [harb, hton]

theorem flag_sol_ton_consensus (f : VoteFlags) :
    f.solana = true → f.ton = true → flagCount f ≥ 2 := by
  intro hsol hton
  unfold flagCount
  simp [hsol, hton]

/-! =====================================================
    SECTION 14: SINGLE VOTE INSUFFICIENT
    ===================================================== -/

theorem single_chain_insufficient (trace : VoteTrace) :
    totalDistinctChains trace < 2 → ¬hasConsensus trace := by
  intro h hcons
  unfold hasConsensus CONSENSUS_THRESHOLD at hcons
  omega

theorem all_chains_required_for_unanimous (trace : VoteTrace) :
    totalDistinctChains trace = 3 ↔
    chainHasVote trace .arbitrum = true ∧
    chainHasVote trace .solana = true ∧
    chainHasVote trace .ton = true := by
  constructor
  · exact three_votes_implies_all_chains trace
  · intro ⟨harb, hsol, hton⟩
    unfold totalDistinctChains chainHasVote at *
    simp [harb, hsol, hton]

/-! =====================================================
    SECTION 15: OPERATION BINDING
    ===================================================== -/

def voteBelongsToOperation (vote : Vote) (trace : VoteTrace) : Prop :=
  vote.operationId = trace.operationId

def allVotesBound (trace : VoteTrace) : Prop :=
  ∀ v ∈ trace.votes, voteBelongsToOperation v trace

theorem empty_trace_all_bound (opId : Nat) :
    allVotesBound (emptyTrace opId) := by
  unfold allVotesBound emptyTrace
  intro v hv
  exact absurd hv (List.not_mem_nil v)

theorem add_bound_vote_preserves (trace : VoteTrace) (vote : Vote) :
    allVotesBound trace →
    voteBelongsToOperation vote trace →
    allVotesBound (addVote trace vote) := by
  intro h_all h_bound
  unfold allVotesBound addVote at *
  intro v hv
  simp only [List.mem_cons] at hv
  cases hv with
  | inl h => rw [h]; exact h_bound
  | inr h => exact h_all v h

/-! =====================================================
    SECTION 16: TEMPORAL PROPERTIES
    ===================================================== -/

def latestVote (trace : VoteTrace) : Option Vote :=
  trace.votes.head?

theorem add_vote_latest (trace : VoteTrace) (vote : Vote) :
    latestVote (addVote trace vote) = some vote := by
  unfold latestVote addVote
  simp [List.head?]

theorem empty_trace_no_latest (opId : Nat) :
    latestVote (emptyTrace opId) = none := by
  unfold latestVote emptyTrace
  simp [List.head?]

/-! =====================================================
    SECTION 17: BYZANTINE FAULT TOLERANCE
    ===================================================== -/

def MAX_FAULTY : Nat := 1

theorem bft_one_faulty_safe :
    TOTAL_CHAINS - MAX_FAULTY ≥ CONSENSUS_THRESHOLD := by
  unfold TOTAL_CHAINS MAX_FAULTY CONSENSUS_THRESHOLD
  decide

theorem bft_two_faulty_breaks :
    TOTAL_CHAINS - 2 < CONSENSUS_THRESHOLD := by
  unfold TOTAL_CHAINS CONSENSUS_THRESHOLD
  decide

theorem honest_majority_sufficient (honest faulty : Nat) :
    honest + faulty = TOTAL_CHAINS →
    faulty ≤ MAX_FAULTY →
    honest ≥ CONSENSUS_THRESHOLD := by
  intro htotal hfaulty
  unfold TOTAL_CHAINS MAX_FAULTY CONSENSUS_THRESHOLD at *
  omega

/-! =====================================================
    SECTION 18: QUORUM MATHEMATICS
    ===================================================== -/

theorem threshold_is_strict_majority :
    CONSENSUS_THRESHOLD * 2 > TOTAL_CHAINS := by
  unfold CONSENSUS_THRESHOLD TOTAL_CHAINS
  decide

theorem threshold_minimal :
    ∀ t : Nat, t * 2 > TOTAL_CHAINS → t ≥ CONSENSUS_THRESHOLD := by
  intro t h
  unfold TOTAL_CHAINS at h
  unfold CONSENSUS_THRESHOLD
  omega

theorem quorum_intersection :
    2 * CONSENSUS_THRESHOLD > TOTAL_CHAINS := by
  unfold CONSENSUS_THRESHOLD TOTAL_CHAINS
  decide

/-! =====================================================
    SECTION 19: CONSENSUS PAIR DETECTION
    ===================================================== -/

def arbitrumSolanaPair (trace : VoteTrace) : Prop :=
  chainHasVote trace .arbitrum = true ∧ chainHasVote trace .solana = true

def arbitrumTonPair (trace : VoteTrace) : Prop :=
  chainHasVote trace .arbitrum = true ∧ chainHasVote trace .ton = true

def solanaTonPair (trace : VoteTrace) : Prop :=
  chainHasVote trace .solana = true ∧ chainHasVote trace .ton = true

def validConsensusPair (trace : VoteTrace) : Prop :=
  arbitrumSolanaPair trace ∨ arbitrumTonPair trace ∨ solanaTonPair trace

theorem consensus_implies_valid_pair (trace : VoteTrace) :
    hasConsensus trace → validConsensusPair trace := by
  intro h
  unfold hasConsensus CONSENSUS_THRESHOLD totalDistinctChains at h
  unfold validConsensusPair arbitrumSolanaPair arbitrumTonPair solanaTonPair chainHasVote
  cases harb : trace.votes.any (·.chainId == .arbitrum)
  <;> cases hsol : trace.votes.any (·.chainId == .solana)
  <;> cases hton : trace.votes.any (·.chainId == .ton)
  <;> simp_all

theorem valid_pair_implies_consensus (trace : VoteTrace) :
    validConsensusPair trace → hasConsensus trace := by
  intro h
  unfold validConsensusPair arbitrumSolanaPair arbitrumTonPair solanaTonPair at h
  cases h with
  | inl harb_sol => exact consensus_arb_sol trace harb_sol.1 harb_sol.2
  | inr h2 =>
    cases h2 with
    | inl harb_ton => exact consensus_arb_ton trace harb_ton.1 harb_ton.2
    | inr hsol_ton => exact consensus_sol_ton trace hsol_ton.1 hsol_ton.2

theorem consensus_iff_valid_pair (trace : VoteTrace) :
    hasConsensus trace ↔ validConsensusPair trace := by
  constructor
  · exact consensus_implies_valid_pair trace
  · exact valid_pair_implies_consensus trace

/-! =====================================================
    SECTION 20: NO SINGLE CHAIN VETO
    ===================================================== -/

theorem no_arbitrum_veto (trace : VoteTrace) :
    chainHasVote trace .arbitrum = false →
    chainHasVote trace .solana = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro _ hsol hton
  exact consensus_sol_ton trace hsol hton

theorem no_solana_veto (trace : VoteTrace) :
    chainHasVote trace .solana = false →
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro _ harb hton
  exact consensus_arb_ton trace harb hton

theorem no_ton_veto (trace : VoteTrace) :
    chainHasVote trace .ton = false →
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .solana = true →
    hasConsensus trace := by
  intro _ harb hsol
  exact consensus_arb_sol trace harb hsol

end Trinity.VoteTrace
