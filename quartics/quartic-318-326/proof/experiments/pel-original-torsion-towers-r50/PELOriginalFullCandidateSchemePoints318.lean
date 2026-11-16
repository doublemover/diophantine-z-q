module
public import PELOriginalFullCandidatePoints318
public import PELOriginalCandidateChartBase318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public section
noncomputable section
namespace PELOriginalFullCandidateSchemePoints318
open AlgebraicGeometry CategoryTheory Set
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Every genuine Spec(C)-valued point of an actual original affine
chart OVER C is its literal original theta-evaluation morphism. This is
morphism equality, not merely equality of underlying closed points. -/
theorem every_affine_point (j : Label 3)
    (p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (CoordinateChart τ hτ j)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ j))) = 𝟙 _) :
    ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      p = Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom) := by
  obtain ⟨φ,rfl⟩ := Spec.map_surjective p
  have hc : CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j)) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id]
    exact hp
  let f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ :=
    { φ.hom with commutes' := fun c => congrArg (fun h => h.hom c) hc }
  obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  refine ⟨z,hz,?_⟩
  change Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [hf]

/-- EVERY Spec(C)-valued point of the SAME whole reduced projective
candidate over its actual complex structure map comes from an original
theta evaluation through a literal original coordinate chart. All chart
boundaries are covered by the actual nine-chart open cover. -/
theorem every_candidate_point
    (p : Spec (CommRingCat.of ℂ) ⟶ candidate τ hτ)
    (hp : p ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _) :
    ∃ j : Label 3, ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      p = Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom) ≫
        chartMap τ hτ j := by
  let o : Spec (CommRingCat.of ℂ) := IsLocalRing.closedPoint ℂ
  obtain ⟨j,hj⟩ := charts_cover τ hτ (p o)
  have hr : Set.range p ⊆ Set.range (chartMap τ hτ j) := by
    rintro _ ⟨y,rfl⟩
    have hy : y = o := Subsingleton.elim _ _
    subst y
    refine ⟨(actualChartIso τ hτ j).inv ⟨p o,hj⟩,?_⟩
    exact congrArg (candidateChart τ hτ j).ι
      (Iso.inv_hom_id_apply (actualChartIso τ hτ j) ⟨p o,hj⟩)
  let q := IsOpenImmersion.lift (chartMap τ hτ j) p hr
  have hq : q ≫ chartMap τ hτ j = p := IsOpenImmersion.lift_fac _ _ hr
  have hqC : q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ j))) = 𝟙 _ := by
    rw [←chart_over_complex_base,←Category.assoc,hq]
    exact hp
  obtain ⟨z,hz,hzq⟩ := every_affine_point τ hτ j q hqC
  exact ⟨j,z,hz,hq.symm.trans (congrArg (fun q => q ≫ chartMap τ hτ j) hzq)⟩
end PELOriginalFullCandidateSchemePoints318
