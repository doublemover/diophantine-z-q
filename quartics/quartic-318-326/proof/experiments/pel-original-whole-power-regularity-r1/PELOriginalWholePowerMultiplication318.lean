module
public import PELOriginalWholePowerRegularization318
public section
noncomputable section
namespace PELOriginalWholePowerMultiplication318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidatePointEquivalence318
open PELOriginalSectionMultiplication318 PELOriginalWholePowerChartRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual original section multiplication, with the literal degree
identity 3(m+n)=3m+3n discharged, including degree zero. -/
@[expose] def product (m n : ℕ) (s : homogeneous τ hτ (3*m))
    (t : homogeneous τ hτ (3*n)) : homogeneous τ hτ (3*(m+n)) :=
  ⟨s.val*t.val,by rw [Nat.mul_add]; exact product_mem τ hτ (3*m) (3*n) s.val t.val s.property t.property⟩

/-- Full-chart regularization preserves multiplication in ALL degrees.
Thus the compatible linear maps are not unrelated choices of regular
functions at separate section levels. -/
theorem regularize_product (m n : ℕ) (j : Label 3)
    (s : homogeneous τ hτ (3*m)) (t : homogeneous τ hτ (3*n)) :
    PELOriginalWholePowerRegularization318.linear τ hτ (m+n) j (product τ hτ m n s t) =
      PELOriginalWholePowerRegularization318.linear τ hτ m j s *
      PELOriginalWholePowerRegularization318.linear τ hτ n j t := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  rw [map_mul,PELOriginalWholePowerRegularization318.evaluation,
    PELOriginalWholePowerRegularization318.evaluation,PELOriginalWholePowerRegularization318.evaluation]
  change (s.val _*t.val _)/(_^(m+n))=(s.val _/_^m)*(t.val _/_^n)
  rw [pow_add,div_mul_div_comm]

@[expose] def constant (c : ℂ) : homogeneous τ hτ (3*0) :=
  ⟨fun _ => c,constant_mem τ hτ c⟩

/-- Actual coefficient-ring normalization in degree zero. -/
theorem regularize_constant (j : Label 3) (c : ℂ) :
    PELOriginalWholePowerRegularization318.linear τ hτ 0 j (constant τ hτ c)=algebraMap ℂ _ c := by
  apply PELOriginalChartPointSeparation318.ext τ hτ j
  intro f
  rw [PELOriginalWholePowerRegularization318.evaluation,f.commutes]
  change c/(_^0)=c
  simp only [pow_zero,div_one]
end PELOriginalWholePowerMultiplication318
