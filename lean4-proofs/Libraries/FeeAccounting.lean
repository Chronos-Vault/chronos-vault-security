/-
  FeeAccountingLib - Fee Calculation and Distribution
  Formal verification of fee mechanics
  
  Mathematical proofs for fee calculation correctness.
-/

namespace Libraries.FeeAccounting

/-! ## Constants -/

def BPS_DENOMINATOR : Nat := 10000
def PROTOCOL_FEE_BPS : Nat := 30       -- 0.30%
def KEEPER_FEE_BPS : Nat := 10         -- 0.10%
def RELAYER_FEE_BPS : Nat := 5         -- 0.05%
def MAX_TOTAL_FEE_BPS : Nat := 100     -- 1% max

/-! ## Fee Structures -/

structure FeeConfig where
  protocolFeeBps : Nat
  keeperFeeBps : Nat
  relayerFeeBps : Nat
  treasuryAddress : ByteArray
deriving Repr

structure FeeDistribution where
  protocolFee : Nat
  keeperFee : Nat
  relayerFee : Nat
  netAmount : Nat
deriving Repr

/-! ## Fee Calculations -/

def calculateFee (amount : Nat) (feeBps : Nat) : Nat :=
  (amount * feeBps) / BPS_DENOMINATOR

def calculateTotalFee (amount : Nat) (config : FeeConfig) : Nat :=
  calculateFee amount config.protocolFeeBps +
  calculateFee amount config.keeperFeeBps +
  calculateFee amount config.relayerFeeBps

def distributeFees (amount : Nat) (config : FeeConfig) : FeeDistribution :=
  let protocolFee := calculateFee amount config.protocolFeeBps
  let keeperFee := calculateFee amount config.keeperFeeBps
  let relayerFee := calculateFee amount config.relayerFeeBps
  let totalFee := protocolFee + keeperFee + relayerFee
  {
    protocolFee := protocolFee
    keeperFee := keeperFee
    relayerFee := relayerFee
    netAmount := amount - totalFee
  }

/-! ## Predicates -/

def validFeeConfig (config : FeeConfig) : Prop :=
  config.protocolFeeBps + config.keeperFeeBps + config.relayerFeeBps ≤ MAX_TOTAL_FEE_BPS

/-! ## Key Theorems -/

theorem protocol_fee_0_3_percent : PROTOCOL_FEE_BPS = 30 := rfl

theorem max_total_fee_1_percent : MAX_TOTAL_FEE_BPS = 100 := rfl

theorem bps_denominator_value : BPS_DENOMINATOR = 10000 := rfl

/-- Each individual fee is bounded by amount -/
theorem fee_bounded_by_amount (amount feeBps : Nat) :
    calculateFee amount feeBps ≤ amount := by
  unfold calculateFee BPS_DENOMINATOR
  exact Nat.div_le_self (amount * feeBps) 10000

/-- Total fee is sum of component fees -/
theorem total_fee_is_sum (amount : Nat) (config : FeeConfig) :
    calculateTotalFee amount config = 
    calculateFee amount config.protocolFeeBps +
    calculateFee amount config.keeperFeeBps +
    calculateFee amount config.relayerFeeBps := rfl

/-- Zero amount yields zero fee -/
theorem zero_amount_zero_fee (feeBps : Nat) :
    calculateFee 0 feeBps = 0 := by
  unfold calculateFee BPS_DENOMINATOR
  simp

/-- Zero fee rate yields zero fee -/
theorem zero_rate_zero_fee (amount : Nat) :
    calculateFee amount 0 = 0 := by
  unfold calculateFee BPS_DENOMINATOR
  simp

/-- Fee is monotonic in amount -/
theorem fee_monotonic_amount (amount1 amount2 feeBps : Nat) :
    amount1 ≤ amount2 → calculateFee amount1 feeBps ≤ calculateFee amount2 feeBps := by
  intro h
  unfold calculateFee BPS_DENOMINATOR
  exact Nat.div_le_div_right (Nat.mul_le_mul_right feeBps h)

/-- Fee is monotonic in rate -/
theorem fee_monotonic_rate (amount rate1 rate2 : Nat) :
    rate1 ≤ rate2 → calculateFee amount rate1 ≤ calculateFee amount rate2 := by
  intro h
  unfold calculateFee BPS_DENOMINATOR
  exact Nat.div_le_div_right (Nat.mul_le_mul_left amount h)

/-! ## Distribution Conservation -/

/-- Distribution total is bounded by original amount -/
theorem distribution_total_bounded (amount : Nat) (config : FeeConfig) :
    let dist := distributeFees amount config
    dist.protocolFee + dist.keeperFee + dist.relayerFee ≤ amount := by
  unfold distributeFees
  simp only
  have h1 := fee_bounded_by_amount amount config.protocolFeeBps
  have h2 := fee_bounded_by_amount amount config.keeperFeeBps
  have h3 := fee_bounded_by_amount amount config.relayerFeeBps
  calc calculateFee amount config.protocolFeeBps + 
       calculateFee amount config.keeperFeeBps + 
       calculateFee amount config.relayerFeeBps
    ≤ amount + amount + amount := by
        apply Nat.add_le_add
        apply Nat.add_le_add
        exact h1
        exact h2
        exact h3
    _ = 3 * amount := by ring
    _ ≥ calculateFee amount config.protocolFeeBps + 
        calculateFee amount config.keeperFeeBps + 
        calculateFee amount config.relayerFeeBps := by
        apply Nat.add_le_add
        apply Nat.add_le_add
        exact h1
        exact h2
        exact h3

/-- Net amount plus fees equals original when no overflow -/
theorem distribution_exact_conservation (amount : Nat) (config : FeeConfig) 
    (h_no_overflow : calculateTotalFee amount config ≤ amount) :
    let dist := distributeFees amount config
    dist.protocolFee + dist.keeperFee + dist.relayerFee + dist.netAmount = amount := by
  unfold distributeFees calculateTotalFee at *
  simp only
  have : amount - (calculateFee amount config.protocolFeeBps + 
         calculateFee amount config.keeperFeeBps + 
         calculateFee amount config.relayerFeeBps) + 
         (calculateFee amount config.protocolFeeBps + 
          calculateFee amount config.keeperFeeBps + 
          calculateFee amount config.relayerFeeBps) = amount := 
    Nat.sub_add_cancel h_no_overflow
  linarith

end Libraries.FeeAccounting
