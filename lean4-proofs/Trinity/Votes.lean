/-
  Trinity Protocol - Vote Trace Module
  Rigorous invariant modeling for validator vote tracking
  
  This module models the on-chain vote submission and tracking
  mechanism used by the Trinity 2-of-3 consensus system.
  
  All theorems proven - ZERO `sorry` statements
  Mathlib-free for portability and fast compilation
-/

namespace Trinity.Votes

/-! ## Chain Identifiers -/

inductive ChainId where
  | arbitrum : ChainId
  | solana : ChainId  
  | ton : ChainId
deriving DecidableEq, Repr, Inhabited

def ChainId.toNat : ChainId → Nat
  | .arbitrum => 1
  | .solana => 2  
  | .ton => 3

/-! ## Vote Record Structure -/

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

/-! ## Vote Counting -/

def voteCount (trace : VoteTrace) : Nat :=
  trace.votes.length

def chainHasVote (trace : VoteTrace) (chain : ChainId) : Bool :=
  trace.votes.any (·.chainId == chain)

def countDistinctChains (trace : VoteTrace) : Nat :=
  let hasArb := trace.votes.any (·.chainId == .arbitrum)
  let hasSol := trace.votes.any (·.chainId == .solana)
  let hasTon := trace.votes.any (·.chainId == .ton)
  (if hasArb then 1 else 0) + (if hasSol then 1 else 0) + (if hasTon then 1 else 0)

/-! ## Vote Operations -/

def addVote (trace : VoteTrace) (vote : Vote) : VoteTrace :=
  { trace with votes := vote :: trace.votes }

def emptyTrace (opId : Nat) : VoteTrace :=
  { votes := [], operationId := opId }

/-! ## Uniqueness Predicate -/

def uniqueChainVotes (trace : VoteTrace) : Prop :=
  ∀ v1 v2 : Vote, v1 ∈ trace.votes → v2 ∈ trace.votes → 
  v1.chainId = v2.chainId → v1 = v2

/-! ## Core Theorems -/

/-- Empty trace has no votes -/
theorem empty_trace_count (opId : Nat) :
    voteCount (emptyTrace opId) = 0 := rfl

/-- Adding vote increases count by 1 -/
theorem add_vote_count (trace : VoteTrace) (vote : Vote) :
    voteCount (addVote trace vote) = voteCount trace + 1 := by
  unfold addVote voteCount
  simp [List.length_cons]

/-- Added vote is present -/
theorem added_vote_present (trace : VoteTrace) (vote : Vote) :
    chainHasVote (addVote trace vote) vote.chainId = true := by
  unfold addVote chainHasVote
  simp [List.any_cons]

/-- Existing votes preserved when adding -/
theorem add_preserves_existing (trace : VoteTrace) (vote : Vote) (chain : ChainId) :
    chainHasVote trace chain = true → chainHasVote (addVote trace vote) chain = true := by
  intro h
  unfold addVote chainHasVote at *
  simp only [List.any_cons, Bool.or_eq_true]
  right
  exact h

/-! ## 2-of-3 Consensus Properties -/

def CONSENSUS_THRESHOLD : Nat := 2
def TOTAL_CHAINS : Nat := 3

def hasConsensus (trace : VoteTrace) : Prop :=
  countDistinctChains trace ≥ CONSENSUS_THRESHOLD

/-- Single distinct chain insufficient for consensus -/
theorem single_distinct_insufficient (trace : VoteTrace) :
    countDistinctChains trace < 2 → ¬hasConsensus trace := by
  intro h hcons
  unfold hasConsensus CONSENSUS_THRESHOLD at hcons
  omega

/-- Two distinct chain votes achieve consensus -/
theorem two_chains_consensus (trace : VoteTrace) :
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .solana = true →
    hasConsensus trace := by
  intro harb hsol
  unfold hasConsensus CONSENSUS_THRESHOLD countDistinctChains chainHasVote at *
  simp [harb, hsol]

theorem two_chains_arb_ton (trace : VoteTrace) :
    chainHasVote trace .arbitrum = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro harb hton
  unfold hasConsensus CONSENSUS_THRESHOLD countDistinctChains chainHasVote at *
  simp [harb, hton]

theorem two_chains_sol_ton (trace : VoteTrace) :
    chainHasVote trace .solana = true →
    chainHasVote trace .ton = true →
    hasConsensus trace := by
  intro hsol hton
  unfold hasConsensus CONSENSUS_THRESHOLD countDistinctChains chainHasVote at *
  simp [hsol, hton]

/-- Max 3 distinct chains possible -/
theorem max_distinct_chains (trace : VoteTrace) :
    countDistinctChains trace ≤ 3 := by
  unfold countDistinctChains
  cases trace.votes.any (·.chainId == .arbitrum)
  <;> cases trace.votes.any (·.chainId == .solana)
  <;> cases trace.votes.any (·.chainId == .ton)
  <;> simp

/-! ## Safety Properties -/

/-- Votes cannot be removed -/
theorem votes_monotonic (trace : VoteTrace) (vote : Vote) :
    voteCount trace ≤ voteCount (addVote trace vote) := by
  rw [add_vote_count]
  exact Nat.le_add_right _ 1

/-- Operation ID preserved -/
theorem op_id_preserved (trace : VoteTrace) (vote : Vote) :
    (addVote trace vote).operationId = trace.operationId := rfl

/-- Empty trace has no votes for any chain -/
theorem empty_no_votes (opId : Nat) (chain : ChainId) :
    chainHasVote (emptyTrace opId) chain = false := by
  unfold emptyTrace chainHasVote
  simp [List.any]

/-- Empty trace satisfies uniqueness -/
theorem empty_unique (opId : Nat) :
    uniqueChainVotes (emptyTrace opId) := by
  unfold uniqueChainVotes emptyTrace
  intro v1 v2 hv1 _ _
  exact absurd hv1 (List.not_mem_nil v1)

/-- Empty trace has zero distinct chains -/
theorem empty_zero_distinct (opId : Nat) :
    countDistinctChains (emptyTrace opId) = 0 := by
  unfold emptyTrace countDistinctChains
  simp [List.any]

/-- Empty trace has no consensus -/
theorem empty_no_consensus (opId : Nat) :
    ¬hasConsensus (emptyTrace opId) := by
  unfold hasConsensus CONSENSUS_THRESHOLD
  rw [empty_zero_distinct]
  omega

/-! ## Byzantine Fault Tolerance -/

def MAX_FAULTY : Nat := 1

theorem bft_tolerates_one :
    TOTAL_CHAINS - MAX_FAULTY ≥ CONSENSUS_THRESHOLD := by
  unfold TOTAL_CHAINS MAX_FAULTY CONSENSUS_THRESHOLD
  decide

theorem bft_fails_at_two :
    TOTAL_CHAINS - 2 < CONSENSUS_THRESHOLD := by
  unfold TOTAL_CHAINS CONSENSUS_THRESHOLD
  decide

theorem quorum_intersection :
    2 * CONSENSUS_THRESHOLD > TOTAL_CHAINS := by
  unfold CONSENSUS_THRESHOLD TOTAL_CHAINS
  decide

end Trinity.Votes
