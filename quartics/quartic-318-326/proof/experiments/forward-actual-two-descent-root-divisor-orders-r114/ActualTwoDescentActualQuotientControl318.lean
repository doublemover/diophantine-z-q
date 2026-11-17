module
public import ActualTwoDescentBetaPointCardinalityBridge318
public section
noncomputable section
namespace ActualTwoDescentActualQuotientControl318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentSameRationalBounds318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentActualQuotientBound318 ActualTwoDescentBetaPointCardinalityBridge318
open ActualTwoDescentPointExtraction318

/-- Actual global rational quotient control, separate from the cardinality of
local candidate classes. The final implication records the exact missing input. -/
def QuotientControl (n b : ℕ) : Prop :=
  RationalEightBound n b ∧ Finite (DoubleQuotient (n : ℚ)) ∧
  Nat.card (DoubleQuotient (n : ℚ)) ≤ 8 ∧
  (Nat.card (DoubleQuotient (n : ℚ))=8 → Nonempty (KummerPoint (b : ℚ) (n : ℚ)))

lemma actual_quotient_control (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0) (H : RationalEightBound n b) :
    QuotientControl n b := by
  obtain ⟨hf,hbound⟩ := actual_quotient_finite_bound n b hn hb H
  exact ⟨H,hf,hbound,actual_beta_point_of_quotient_eight n b hn hb H⟩

end ActualTwoDescentActualQuotientControl318
