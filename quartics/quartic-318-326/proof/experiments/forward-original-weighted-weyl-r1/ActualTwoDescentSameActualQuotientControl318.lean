module
public import ActualTwoDescentActualQuotientControl318
public section
noncomputable section
namespace ActualTwoDescentSameActualQuotientControl318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentActualQuotientControl318 ActualTwoDescentSameRationalBounds318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentSmallPattern318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open scoped BigOperators

/-- The SAME original beta and SAME final support produce actual global
quotient bounds on both twists, not independent unrelated constructions. -/
theorem actual_same_quotient_control (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (qB : BetaIndex d → ℕ)
    (hB : ∀ b, p (some (Sum.inl (Sum.inl b)))=qB b) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    QuotientControl (∏ i, p i) (∏ b, qB b) ∧
    QuotientControl (∏ i, restricted p i) (∏ b, qB b) := by
  obtain ⟨H,H0⟩ := actual_same_rational_bounds d p hd qB hB N C C0
  have hp : ∀ i, p i ≠ 0 := fun i => (Fact.out : (p i).Prime).ne_zero
  have hb : (∏ b, qB b) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    rw [←hB b]
    exact hp _
  constructor
  · exact actual_quotient_control _ _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hb H
  · exact actual_quotient_control _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp (oldEmbedding i))) hb H0

end ActualTwoDescentSameActualQuotientControl318
