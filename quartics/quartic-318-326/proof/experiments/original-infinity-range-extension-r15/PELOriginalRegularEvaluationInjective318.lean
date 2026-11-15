module
public import FourRootCoordinateMonomialSpanning318
public import PELOriginalRegularCoefficientSeparation318
public section
noncomputable section
namespace PELOriginalRegularEvaluationInjective318
open scoped BigOperators
open PELOriginalRegularCoordinateAlgebra318
open PELOriginalContactRootFunctions318 PELOriginalCommonContactBase318
open FourRootCoordinateMonomialSpanning318
local instance : Algebra (Polynomial ℂ) CoordinateRing :=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate branches none)).toAlgebra

lemma scalar_value (x : OriginalRegular) (p : Polynomial ℂ) :
    atPoint x (algebraMap (Polynomial ℂ) CoordinateRing p) = p.eval (base x.val) := by
  change atPoint x (Polynomial.aeval
    (FourRootAffineCoordinateRing318.coordinate branches none) p) = _
  rw [← Polynomial.aeval_algHom_apply,atPoint_base]
  rfl

lemma monomial_value (x : OriginalRegular) (m : FourRootSignCoefficientExtraction318.Mask) :
    atPoint x (rootMonomial branches m) =
      FourRootSignCoefficientExtraction318.monomial (roots x.val) m := by
  unfold rootMonomial FourRootSignCoefficientExtraction318.monomial
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases hm : m i <;> simp [hm,atPoint_root]

/-- The full literal coordinate algebra embeds into functions on the
actual original regular source. The proof uses all original root tuples
and polynomial coefficient extraction, not a presumed field comparison. -/
theorem evaluation_injective : Function.Injective evaluation := by
  suffices hk : ∀ a : CoordinateRing, evaluation a = 0 → a = 0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hk
    rw [map_sub,hab,sub_self]
  intro a ha
  obtain ⟨c,hc⟩ := decomposition branches a
  have hvalues : ∀ x : OriginalRegular,
      (∑ m, (c m).eval (base x.val) *
        FourRootSignCoefficientExtraction318.monomial (roots x.val) m) = 0 := by
    intro x
    have h := congrArg (atPoint x) hc
    rw [map_sum] at h
    have hs : ∀ m, atPoint x (c m • rootMonomial branches m) =
        (c m).eval (base x.val) *
          FourRootSignCoefficientExtraction318.monomial (roots x.val) m := by
      intro m
      rw [Algebra.smul_def,map_mul,scalar_value,monomial_value]
    simp_rw [hs] at h
    have hz : atPoint x a = 0 := congrFun ha x
    exact h.trans hz
  have hz := PELOriginalRegularCoefficientSeparation318.coefficients_zero c hvalues
  rw [← hc]
  simp only [hz,zero_smul,Finset.sum_const_zero]
end PELOriginalRegularEvaluationInjective318
