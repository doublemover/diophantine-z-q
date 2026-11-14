module
public import PELOriginalExponentialLatticeCharacter318
public import PELOriginalBalancedThetaProducts318
public import PELOriginalNonzeroThetaSection318
public section
noncomputable section
namespace PELOriginalThetaTranslationPeriod318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318
open PELOriginalPolarizationAutomorphy318 PELOriginalBalancedThetaProducts318
open PELOriginalExponentialLatticeCharacter318
variable (τ:ℂ)(hτ:0<τ.im)
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- Compare the SAME original theta automorphy square at one produced
nonzero value. Constants cancel only after proving every canceled factor
nonzero. No global zero-free theta or logarithm is assumed. -/
lemma character_of_translate(δ:ComplexVectors)(C:ℂ)(hC:C≠0)
    (ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (ht:∀a,F (a+δ)=C*Complex.exp (ℓ a)*F a)(l:L τ hτ):
    Complex.exp (ℓ l.val)=Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val):=by
  obtain ⟨z,hz⟩:=PELOriginalNonzeroThetaSection318.exists_original_value_nonzero τ hτ
  have he:C*Complex.exp (ℓ z)*Complex.exp (ℓ l.val)*factor τ hτ l z*F z=
      C*Complex.exp (ℓ z)*Complex.exp ((Real.pi:ℂ)*form τ hτ δ l.val)*
        factor τ hτ l z*F z:=by
    have h:=ht (z+l.val)
    rw [show z+l.val+δ=(z+δ)+l.val by abel,
      PELOriginalGaugedTheta318.original_automorphy,ht z,factor_translate,
      PELOriginalGaugedTheta318.original_automorphy,map_add,Complex.exp_add] at h
    linear_combination -h
  have hn:C*Complex.exp (ℓ z)*factor τ hτ l z*F z≠0:=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hC (Complex.exp_ne_zero _)) (nonzero τ hτ l z)) hz
  apply mul_left_cancel₀ hn
  convert he using 1 <;> ring

/-- A genuine exponential translate symmetry of the actual original
theta can occur ONLY at an original lattice period. Principalness is
consumed at the integral-dual theorem, not presumed from equal j or degree. -/
theorem translate_is_original_period(δ:ComplexVectors)(C:ℂ)(hC:C≠0)
    (ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (ht:∀a,F (a+δ)=C*Complex.exp (ℓ a)*F a):
    δ∈PELOriginalPeriodLattice318.lattice τ hτ:=
  period_of_character τ hτ δ ℓ (character_of_translate τ hτ δ C hC ℓ ht)

/-- The exact original quotient conclusion ready for the separately
constructed triple-product rigidity producer. -/
theorem original_points_equal(x y:ComplexVectors)(C:ℂ)(hC:C≠0)
    (ℓ:ComplexVectors→ₗ[ℂ]ℂ)
    (ht:∀a,F (a+(x-y))=C*Complex.exp (ℓ a)*F a):
    DiscreteComplexPeriodAtlas318.projection (PELOriginalPolarizationTransitions318.P τ) x=
      DiscreteComplexPeriodAtlas318.projection (PELOriginalPolarizationTransitions318.P τ) y:=by
  have hm:=translate_is_original_period τ hτ (x-y) C hC ℓ ht
  have hp:x-y∈PELOriginalPolarizationTransitions318.P τ:=by
    rw [PELOriginalPeriodLattice318.exact_period_subgroup τ hτ]
    exact hm
  change QuotientAddGroup.mk x=QuotientAddGroup.mk y
  exact QuotientAddGroup.eq_iff_sub_mem.mpr hp
end PELOriginalThetaTranslationPeriod318
