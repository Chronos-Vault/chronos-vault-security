/-
  ConsensusProposalLib - Proposal Management
  Formal verification of consensus proposal lifecycle
-/

import Mathlib.Data.Nat.Basic

namespace Libraries.ConsensusProposal

/-! ## Constants -/

def PROPOSAL_EXPIRY : Nat := 604800    -- 7 days
def MIN_VOTING_PERIOD : Nat := 86400   -- 1 day
def MAX_VOTING_PERIOD : Nat := 604800  -- 7 days
def EXECUTION_DELAY : Nat := 172800    -- 48 hours

/-! ## Proposal State -/

inductive ProposalStatus where
  | draft : ProposalStatus
  | active : ProposalStatus
  | passed : ProposalStatus
  | rejected : ProposalStatus
  | executed : ProposalStatus
  | expired : ProposalStatus
  | canceled : ProposalStatus
deriving DecidableEq, Repr

structure Proposal where
  id : Nat
  proposer : ByteArray
  target : ByteArray
  data : ByteArray
  value : Nat
  status : ProposalStatus
  votesFor : Nat
  votesAgainst : Nat
  createdAt : Nat
  votingEndsAt : Nat
  executionTime : Option Nat
deriving Repr

/-! ## Predicates -/

def isActive (prop : Proposal) (currentTime : Nat) : Prop :=
  prop.status = ProposalStatus.active ∧
  currentTime ≤ prop.votingEndsAt

def hasPassed (prop : Proposal) : Prop :=
  prop.votesFor > prop.votesAgainst

def canExecute (prop : Proposal) (currentTime : Nat) : Prop :=
  prop.status = ProposalStatus.passed ∧
  match prop.executionTime with
  | some t => currentTime ≥ t
  | none => False

def isExpired (prop : Proposal) (currentTime : Nat) : Prop :=
  currentTime > prop.createdAt + PROPOSAL_EXPIRY

def validVotingPeriod (createdAt votingEndsAt : Nat) : Prop :=
  let duration := votingEndsAt - createdAt
  duration ≥ MIN_VOTING_PERIOD ∧ duration ≤ MAX_VOTING_PERIOD

/-! ## State Transitions -/

def voteFor (prop : Proposal) (weight : Nat) : Proposal :=
  { prop with votesFor := prop.votesFor + weight }

def voteAgainst (prop : Proposal) (weight : Nat) : Proposal :=
  { prop with votesAgainst := prop.votesAgainst + weight }

def finalize (prop : Proposal) : Proposal :=
  if prop.votesFor > prop.votesAgainst then
    { prop with status := ProposalStatus.passed }
  else
    { prop with status := ProposalStatus.rejected }

def execute (prop : Proposal) : Proposal :=
  { prop with status := ProposalStatus.executed }

def cancel (prop : Proposal) : Proposal :=
  { prop with status := ProposalStatus.canceled }

def expire (prop : Proposal) : Proposal :=
  { prop with status := ProposalStatus.expired }

/-! ## Key Theorems -/

theorem vote_for_increases (prop : Proposal) (weight : Nat) :
  weight > 0 →
  (voteFor prop weight).votesFor > prop.votesFor := by
  intro h
  unfold voteFor
  simp
  omega

theorem vote_against_increases (prop : Proposal) (weight : Nat) :
  weight > 0 →
  (voteAgainst prop weight).votesAgainst > prop.votesAgainst := by
  intro h
  unfold voteAgainst
  simp
  omega

theorem majority_determines_outcome (prop : Proposal) :
  let finalized := finalize prop
  (prop.votesFor > prop.votesAgainst → finalized.status = ProposalStatus.passed) ∧
  (prop.votesFor ≤ prop.votesAgainst → finalized.status = ProposalStatus.rejected) := by
  unfold finalize
  constructor
  · intro h; simp [h]
  · intro h; simp [Nat.not_lt.mpr h]

theorem execute_is_final (prop : Proposal) :
  (execute prop).status = ProposalStatus.executed := by
  unfold execute
  rfl

theorem canceled_blocks_execution (prop : Proposal) (currentTime : Nat) :
  prop.status = ProposalStatus.canceled →
  ¬canExecute prop currentTime := by
  intro h hexec
  unfold canExecute at hexec
  simp [h] at hexec

/-! ## Timing Bounds -/

theorem execution_delay_48h : EXECUTION_DELAY = 172800 := rfl

theorem min_voting_1_day : MIN_VOTING_PERIOD = 86400 := rfl

theorem max_voting_7_days : MAX_VOTING_PERIOD = 604800 := rfl

theorem voting_period_bounded (createdAt votingEndsAt : Nat) :
  validVotingPeriod createdAt votingEndsAt →
  votingEndsAt ≥ createdAt + MIN_VOTING_PERIOD ∧
  votingEndsAt ≤ createdAt + MAX_VOTING_PERIOD := by
  intro h
  unfold validVotingPeriod at h
  omega

end Libraries.ConsensusProposal
