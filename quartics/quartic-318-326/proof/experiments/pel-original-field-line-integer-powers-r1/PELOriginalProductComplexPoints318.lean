module
public import PELOriginalProductChartCover318
public import PELOriginalChartSchemePointIdentity318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace PELOriginalProductComplexPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateComplexPoints318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProductChartCover318 PELOriginalProductChartPoints318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def baseMap : Product τ hτ ⟶ Spec (CommRingCat.of ℂ) :=
  pullback.fst (π τ hτ) (π τ hτ)≫π τ hτ

instance productFiniteType : LocallyOfFiniteType (baseMap τ hτ) := by
  dsimp [baseMap]
  infer_instance

/-- The true ordered pair of original candidate Spec(C) points. -/
@[expose] def pair (q r : Base τ) : Spec (CommRingCat.of ℂ) ⟶ Product τ hτ :=
  pullback.lift (candidateComplexPoint τ hτ q) (candidateComplexPoint τ hτ r)
    ((PELOriginalProperComplexCandidate318.candidate_point_over τ hτ q).trans
      (PELOriginalProperComplexCandidate318.candidate_point_over τ hτ r).symm)

@[reassoc] lemma pair_fst (q r : Base τ) :
    pair τ hτ q r≫pullback.fst _ _=candidateComplexPoint τ hτ q := pullback.lift_fst _ _ _
@[reassoc] lemma pair_snd (q r : Base τ) :
    pair τ hτ q r≫pullback.snd _ _=candidateComplexPoint τ hτ r := pullback.lift_snd _ _ _
@[reassoc] lemma pair_over (q r : Base τ) : pair τ hτ q r≫baseMap τ hτ=𝟙 _ := by
  rw [baseMap,←Category.assoc,pair_fst]
  exact PELOriginalProperComplexCandidate318.candidate_point_over τ hτ q

/-- Every genuine over-C point of the whole product is a literal
ordered pair of original torus points, as an equality of morphisms. -/
theorem every_point (p : Spec (CommRingCat.of ℂ) ⟶ Product τ hτ)
    (hp : p≫baseMap τ hτ=𝟙 _) :
    ∃ z a : ComplexVectors, p=pair τ hτ (projection (P τ) z) (projection (P τ) a) := by
  have hleft : (p≫pullback.fst (π τ hτ) (π τ hτ))≫π τ hτ=𝟙 _ := by
    simpa only [baseMap,Category.assoc] using hp
  have hright : (p≫pullback.snd (π τ hτ) (π τ hτ))≫π τ hτ=𝟙 _ := by
    rw [Category.assoc,←pullback.condition]
    exact hp
  obtain ⟨j,z,hz,hze⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ _ hleft
  obtain ⟨k,a,ha,hae⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ _ hright
  refine ⟨z,a,?_⟩
  apply pullback.hom_ext
  · rw [pair_fst,hze,PELOriginalChartSchemePointIdentity318.chart_point]
  · rw [pair_snd,hae,PELOriginalChartSchemePointIdentity318.chart_point]

lemma pair_injective : Function.Injective (fun qr : Base τ × Base τ => pair τ hτ qr.1 qr.2) := by
  intro qr st h
  apply Prod.ext
  · apply PELOriginalChartSchemePointIdentity318.candidate_point_injective τ hτ
    simpa only [pair_fst] using congrArg (fun f => f≫pullback.fst (π τ hτ) (π τ hτ)) h
  · apply PELOriginalChartSchemePointIdentity318.candidate_point_injective τ hτ
    simpa only [pair_snd] using congrArg (fun f => f≫pullback.snd (π τ hτ) (π τ hτ)) h

/-- Exact square from actual tensor evaluation to the actual product
point. Thus regular matrix values are values of the true binary scheme
charts, not merely of an abstract tensor model. -/
theorem chart_pair (j k : Label 3) (z a : ComplexVectors)
    (hz : PELOriginalLevelPowerSections318.value τ hτ 3 j z ≠ 0)
    (ha : PELOriginalLevelPowerSections318.value τ hτ 3 k a ≠ 0) :
    Spec.map (CommRingCat.ofHom
      (TensorComplexPointSeparation318.evaluation (algebraEvaluation τ hτ z j hz)
        (algebraEvaluation τ hτ a k ha)).toRingHom)≫chartInclusion τ hτ (j,k)=
      pair τ hτ (projection (P τ) z) (projection (P τ) a) := by
  apply pullback.hom_ext
  · rw [Category.assoc,inclusion_fst,←Category.assoc,←Spec.map_comp,pair_fst]
    have he : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        CoordinateChart τ hτ j →+* ProductRing τ hτ j k)≫
        CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
          (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom=
        CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom := by
      ext x
      simp [TensorComplexPointSeparation318.evaluation]
    rw [he,PELOriginalChartSchemePointIdentity318.chart_point]
  · rw [Category.assoc,inclusion_snd,←Category.assoc,←Spec.map_comp,pair_snd]
    have he : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        CoordinateChart τ hτ k →ₐ[ℂ] ProductRing τ hτ j k).toRingHom≫
        CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
          (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom=
        CommRingCat.ofHom (algebraEvaluation τ hτ a k ha).toRingHom := by
      ext x
      simp [TensorComplexPointSeparation318.evaluation]
    rw [he,PELOriginalChartSchemePointIdentity318.chart_point]

@[reassoc] lemma chart_over (j k : Label 3) :
    chartInclusion τ hτ (j,k)≫baseMap τ hτ=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ProductRing τ hτ j k))) := by
  rw [baseMap,←Category.assoc,inclusion_fst,Category.assoc,
    PELOriginalCandidateChartBase318.chart_over_complex_base,←Spec.map_comp]
  congr 1
  ext c
  exact (Algebra.TensorProduct.includeLeft : CoordinateChart τ hτ j →ₐ[ℂ]
    ProductRing τ hτ j k).commutes c
/-- Full reduced-scheme equality from every actual original ordered pair. -/
theorem morphism_ext
    (f g : Product τ hτ ⟶ PELOriginalReducedProjectiveCandidate318.candidate τ hτ)
    (hf : f≫π τ hτ=baseMap τ hτ) (hg : g≫π τ hτ=baseMap τ hτ)
    (h : ∀ z a : ComplexVectors,
      pair τ hτ (projection (P τ) z) (projection (P τ) a)≫f=
        pair τ hτ (projection (P τ) z) (projection (P τ) a)≫g) : f=g := by
  apply ReducedComplexPointMorphisms318.ext (baseMap τ hτ) (π τ hτ) f g hf hg
  intro p hp
  obtain ⟨z,a,rfl⟩ := every_point τ hτ p hp
  exact h z a
end PELOriginalProductComplexPoints318
