module
public import PELOriginalAdditionBasepointFree318
public import PELOriginalHomogeneousRelationVanishing318
public section
noncomputable section
namespace PELOriginalAdditionCandidateRelations318
open scoped TensorProduct
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProductChartPoints318 PELOriginalRegularAdditionTensor318
open PELOriginalCubicRelationIdeal318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma cover_relation (p : Equations) (n : ℕ) (hp : p.IsHomogeneous n)
    (hr : p ∈ relations τ hτ) (z : ComplexVectors) :
    MvPolynomial.eval (fun r => value τ hτ 3 r z) p=0 := by
  obtain ⟨c,hc,he⟩ := actual_cover_scalar τ hτ z
  have h := relation_evaluation τ hτ (DiscreteComplexPeriodAtlas318.projection
    (PELOriginalPolarizationTransitions318.P τ) z) p hr
  rw [←he] at h
  change MvPolynomial.eval (fun r => c*value τ hτ 3 r z) p=0 at h
  rw [HomogeneousEvaluationScaling318.evaluate_scale p n hp] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero n hc)

/-- EVERY original homogeneous candidate relation holds on every
column of the actual regular tensor matrix, as a full product-ring
equality. This is the literal cubic candidate, not a replacement Segre
relation model. -/
theorem column_relation (j k : Label 3) (s : Label 3)
    (p : Equations) (n : ℕ) (hp : p.IsHomogeneous n) (hr : p ∈ relations τ hτ) :
    MvPolynomial.aeval (fun r => coordinate τ hτ j k (r,s)) p=0 := by
  apply PELOriginalProductChartPoints318.ext τ hτ j k
  intro f g
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  obtain ⟨a,ha,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k g
  let e := TensorComplexPointSeparation318.evaluation (algebraEvaluation τ hτ z j hz)
    (algebraEvaluation τ hτ a k ha)
  change e (p.eval₂ (algebraMap ℂ _) (fun r => coordinate τ hτ j k (r,s)))=e 0
  rw [map_zero,MvPolynomial.hom_eval₂]
  have hC : e.toRingHom.comp (algebraMap ℂ (ProductRing τ hτ j k))=RingHom.id ℂ := by
    ext c
    exact e.commutes c
  rw [hC]
  change MvPolynomial.eval (fun r => e (coordinate τ hτ j k (r,s))) p=0
  have hv : (fun r => e (coordinate τ hτ j k (r,s)))=
      fun r => (value τ hτ 3 s (z-a) /
        ((value τ hτ 3 j z)^2*(value τ hτ 3 k a)^2))*value τ hτ 3 r (z+a) := by
    funext r
    rw [show e (coordinate τ hτ j k (r,s))=_ from evaluation τ hτ j k z a hz ha (r,s)]
    ring
  rw [hv,HomogeneousEvaluationScaling318.evaluate_scale p n hp,cover_relation τ hτ p n hp hr,mul_zero]

/-- The SAME full relations also hold on every row, retaining the
literal difference factor as well as the sum factor. -/
theorem row_relation (j k : Label 3) (r : Label 3)
    (p : Equations) (n : ℕ) (hp : p.IsHomogeneous n) (hr : p ∈ relations τ hτ) :
    MvPolynomial.aeval (fun s => coordinate τ hτ j k (r,s)) p=0 := by
  apply PELOriginalProductChartPoints318.ext τ hτ j k
  intro f g
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  obtain ⟨a,ha,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k g
  let e := TensorComplexPointSeparation318.evaluation (algebraEvaluation τ hτ z j hz)
    (algebraEvaluation τ hτ a k ha)
  change e (p.eval₂ (algebraMap ℂ _) (fun s => coordinate τ hτ j k (r,s)))=e 0
  rw [map_zero,MvPolynomial.hom_eval₂]
  have hC : e.toRingHom.comp (algebraMap ℂ (ProductRing τ hτ j k))=RingHom.id ℂ := by
    ext c
    exact e.commutes c
  rw [hC]
  change MvPolynomial.eval (fun s => e (coordinate τ hτ j k (r,s))) p=0
  have hv : (fun s => e (coordinate τ hτ j k (r,s)))=
      fun s => (value τ hτ 3 r (z+a) /
        ((value τ hτ 3 j z)^2*(value τ hτ 3 k a)^2))*value τ hτ 3 s (z-a) := by
    funext s
    rw [show e (coordinate τ hτ j k (r,s))=_ from evaluation τ hτ j k z a hz ha (r,s)]
    ring
  rw [hv,HomogeneousEvaluationScaling318.evaluate_scale p n hp,cover_relation τ hτ p n hp hr,mul_zero]
end PELOriginalAdditionCandidateRelations318
