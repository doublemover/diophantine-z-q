module
public import PELOriginalLevelThetaNegation318
public import PELOriginalChartAnalyticEvaluation318
public import Mathlib.Algebra.MvPolynomial.Rename
public section
noncomputable section
namespace PELOriginalNegationRelations318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalCubicRelationIdeal318 PELOriginalHomogeneousRelationVanishing318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Homogeneous membership is tested on the genuine original covering
vectors; the nonzero scalar between the two actual gauges is canceled. -/
lemma homogeneous_relation_cover (p : Equations) (n : ℕ) (hp : p.IsHomogeneous n) :
    p ∈ relations τ hτ ↔ ∀ z : ComplexVectors,
      MvPolynomial.eval (coverVector τ hτ 1 z) p = 0 := by
  rw [homogeneous_relation_iff τ hτ p n hp]
  constructor
  · intro h z
    obtain ⟨c,hc,he⟩ := actual_cover_scalar τ hτ z
    have hz := h (projection (P τ) z)
    rw [←he] at hz
    change MvPolynomial.eval (fun i => c * coverVector τ hτ 1 z i) p = 0 at hz
    rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero n hc)
  · intro h q
    obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
    obtain ⟨c,hc,he⟩ := actual_cover_scalar τ hτ z
    rw [←he]
    change MvPolynomial.eval (fun i => c * coverVector τ hτ 1 z i) p = 0
    rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp,h z,mul_zero]

/-- Literal polynomial coordinate permutation r ↦ -r in all nine cubic
coordinates; this is an algebra automorphism before any point transport. -/
@[expose] def polynomialNegation : Equations ≃ₐ[ℂ] Equations :=
  MvPolynomial.renameEquiv ℂ (Equiv.neg (Label 3))

lemma polynomialNegation_value (p : Equations) (z : ComplexVectors) :
    MvPolynomial.eval (coverVector τ hτ 1 z) (polynomialNegation p) =
      MvPolynomial.eval (coverVector τ hτ 1 (-z)) p := by
  change MvPolynomial.eval _ (MvPolynomial.rename (fun r : Label 3 => -r) p) = _
  rw [MvPolynomial.eval_rename]
  congr 1
  funext r
  exact (PELOriginalLevelThetaNegation318.value_neg τ hτ 3 r z).symm

lemma polynomialNegation_homogeneous (p : Equations) (n : ℕ) (hp : p.IsHomogeneous n) :
    (polynomialNegation p).IsHomogeneous n := hp.rename_isHomogeneous

lemma polynomialNegation_involutive : Function.Involutive polynomialNegation := by
  intro p
  change MvPolynomial.rename (fun r : Label 3 => -r)
    (MvPolynomial.rename (fun r : Label 3 => -r) p) = p
  rw [MvPolynomial.rename_rename]
  simpa only [Function.comp_def,neg_neg] using MvPolynomial.rename_id_apply p

/-- EVERY mixed-degree actual relation is preserved. The proof first
retains each homogeneous component and its exact formal degree. -/
lemma relation_negation (p : Equations) (hp : p ∈ relations τ hτ) :
    polynomialNegation p ∈ relations τ hτ := by
  rw [←MvPolynomial.sum_homogeneousComponent p,map_sum]
  apply (relations τ hτ).sum_mem
  intro n hn
  apply (homogeneous_relation_cover τ hτ _ n
    (polynomialNegation_homogeneous _ n (MvPolynomial.homogeneousComponent_mem n p))).mpr
  intro z
  rw [polynomialNegation_value]
  exact (homogeneous_relation_cover τ hτ _ n
    (MvPolynomial.homogeneousComponent_mem n p)).mp
      (homogeneous_component_mem τ hτ p hp n) (-z)

lemma relation_negation_iff (p : Equations) :
    polynomialNegation p ∈ relations τ hτ ↔ p ∈ relations τ hτ := by
  constructor
  · intro hp
    simpa only [polynomialNegation_involutive p] using
      relation_negation τ hτ (polynomialNegation p) hp
  · exact relation_negation τ hτ p
end PELOriginalNegationRelations318
