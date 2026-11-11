module
public import PELOriginalComplementaryHermitian318
public import PELOriginalPolarizationAutomorphy318
public section
noncomputable section
namespace PELOriginalComplementaryAutomorphy318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalPeriodLattice318 PELOriginalHermitianForm318 PELPeriodRiemannForm318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationSemicharacter318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual entire-lattice action, not an action on a finite-index substitute. -/
@[expose] def latticeAction (a : order) (l : L τ hτ) : L τ hτ :=
  ⟨linear a l.val,by
    have hl : l.val ∈ periodSubgroup representation order τ := by
      rw [exact_period_subgroup τ hτ]
      exact l.property
    have ha := order_preserves_periods representation order τ a hl
    change linear a l.val ∈ periodSubgroup representation order τ at ha
    rw [exact_period_subgroup τ hτ] at ha
    exact ha⟩

/-- Squaring removes only the genuine integral semicharacter phase.
The two Hermitian contributions add to the SAME original degree-n form.
No unproved flat twist or polarization rescaling is discarded. -/
theorem even_multiplier (a : order) (l : L τ hτ) (z : ComplexVectors) :
    factor τ hτ (latticeAction τ hτ a l) (linear a z)^2 *
      factor τ hτ (latticeAction τ hτ (complement a) l) (linear (complement a) z)^2 =
      factor τ hτ l z^(2*degree a) := by
  have h₁ := hermitian_complement τ hτ a z l.val
  have h₂ := hermitian_complement τ hτ a l.val l.val
  simp only [factor,←Complex.exp_nat_mul,←Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ a l))+
    quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (complement a) l))-
    (degree a:ℤ)*quadratic ((latticeEquiv τ hτ).symm l),?_⟩
  simp only [exponent,latticeAction]
  push_cast
  linear_combination (2*(Real.pi:ℂ))*h₁+(Real.pi:ℂ)*h₂
end PELOriginalComplementaryAutomorphy318
