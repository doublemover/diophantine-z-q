module
public import PELOriginalRatioEvaluationExt318
public section
noncomputable section
namespace PELOriginalRatioRelationEvaluation318
open PELOriginalCandidateAffineCharts318 PELOriginalCubicRelationIdeal318
open PELOriginalChartAnalyticEvaluation318 PELOriginalLevelTheta318
open PELOriginalRatioEvaluationExt318 HomogeneousQuotientChart318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- Every literal homogeneous relation vanishes in the WHOLE ratio
algebra, with no source evaluation or original-image condition. -/
lemma relation_aeval (p : Equations) (hp : p ∈ relations τ hτ) :
    MvPolynomial.aeval (ratioElement τ hτ j) p = 0 := by
  rw [←MvPolynomial.sum_homogeneousComponent p,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [fraction_as_polynomial τ hτ j n _ (MvPolynomial.homogeneousComponent_mem n p)]
  apply Subtype.ext
  change quotientMap (relations τ hτ) j
    (fraction j n (MvPolynomial.homogeneousComponent n p)
      (MvPolynomial.homogeneousComponent_mem n p)) = 0
  apply (fraction_zero_iff (relations τ hτ) j n _ _).mpr
  exact ⟨0,by simpa only [pow_zero,one_mul] using
    PELOriginalCubicRelationIdeal318.homogeneous_component_mem τ hτ p hp n⟩

lemma map_polynomial (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ) (p : Equations) :
    f (MvPolynomial.aeval (ratioElement τ hτ j) p) =
      MvPolynomial.eval (fun i => f (ratioElement τ hτ j i)) p := by
  have hc : f.toRingHom.comp (algebraMap ℂ (CoordinateChart τ hτ j)) = RingHom.id ℂ := by
    ext c
    exact f.commutes c
  change f (p.eval₂ (algebraMap ℂ _) (ratioElement τ hτ j)) = _
  rw [MvPolynomial.hom_eval₂,hc]
  rfl

lemma point_relations (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ) :
    ∀ p ∈ relations τ hτ, MvPolynomial.eval (fun i => f (ratioElement τ hτ j i)) p = 0 := by
  intro p hp
  rw [←map_polynomial,relation_aeval τ hτ j p hp,map_zero]
end PELOriginalRatioRelationEvaluation318
