module
public import ActualTwoDescentPadicValuationPairs318
public section
noncomputable section
namespace ActualTwoDescentUnitDifferenceParity318
open ActualTwoDescentPadicValuationPairs318
set_option maxHeartbeats 16000000

lemma actual_three_integer_parities (a b c y : ℤ)
    (hab : (a=b ∧ a ≤ 0) ∨ (a=0 ∧ 0 ≤ b) ∨ (0 ≤ a ∧ b=0))
    (hac : (a=c ∧ a ≤ 0) ∨ (a=0 ∧ 0 ≤ c) ∨ (0 ≤ a ∧ c=0))
    (hbc : (b=c ∧ b ≤ 0) ∨ (b=0 ∧ 0 ≤ c) ∨ (0 ≤ b ∧ c=0))
    (hs : a+b+c=2*y) : Even a ∧ Even b ∧ Even c := by
  have hm : a%2=0 ∧ b%2=0 ∧ c%2=0 := by
    rcases hab with hab | hab | hab <;>
      rcases hac with hac | hac | hac <;>
      rcases hbc with hbc | hbc | hbc <;> omega
  exact ⟨⟨a/2,by omega⟩,⟨b/2,by omega⟩,⟨c/2,by omega⟩⟩

/-- A square cubic product whose three factors have pairwise unit
differences has even valuation in every factor, over the actual Q_p. -/
theorem actual_square_cubic_even {p : ℕ} [Fact p.Prime]
    (x a b y : ℚ_[p]) (hx : x ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hxa : x-a ≠ 0) (hxb : x-b ≠ 0) (hab : a-b ≠ 0)
    (vxa : (x-a).valuation=0) (vxb : (x-b).valuation=0) (vab : (a-b).valuation=0)
    (hcurve : y^2=x*a*b) : Even x.valuation ∧ Even a.valuation ∧ Even b.valuation := by
  have hval := congrArg Padic.valuation hcurve
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero hx ha) hb,
    Padic.valuation_mul hx ha] at hval
  exact actual_three_integer_parities x.valuation a.valuation b.valuation y.valuation
    (actual_unit_difference_pair x a hx ha hxa vxa)
    (actual_unit_difference_pair x b hx hb hxb vxb)
    (actual_unit_difference_pair a b ha hb hab vab) hval.symm

end ActualTwoDescentUnitDifferenceParity318
