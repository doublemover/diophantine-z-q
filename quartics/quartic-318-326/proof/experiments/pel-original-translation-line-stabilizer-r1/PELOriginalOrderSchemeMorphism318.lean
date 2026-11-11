module
public import PELOriginalOrderChartMorphism318
public import ReducedComplexPointMorphisms318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace PELOriginalOrderSchemeMorphism318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalChartAnalyticEvaluation318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318 QuaternionicOrderPeriodQuotient318
variable (τ : ℂ) (hτ : 0<τ.im) (a₀ : order)
local instance chartDomain (j : Label 3) : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFinite (j : Label 3) : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) :=
  chart_finite_type τ hτ j
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ
local instance standardGrading : GradedAlgebra (ComplexProjectiveMarkerPoint318.grading (ι := Label 3)) :=
  MvPolynomial.gradedAlgebra

/-- Agreement on the ACTUAL scheme pullback of any two original cubic
charts. Reducedness comes from the actual open immersion, and the
finite-type/separated point criterion is used only after every C-valued
point is computed by its true original source representative. -/
theorem compatible (j k : Label 3) :
    pullback.fst (chartMap τ hτ j) (chartMap τ hτ k)≫
      PELOriginalOrderChartMorphism318.morphism τ hτ a₀ j=
    pullback.snd (chartMap τ hτ j) (chartMap τ hτ k)≫
      PELOriginalOrderChartMorphism318.morphism τ hτ a₀ k := by
  let a := chartMap τ hτ j
  let b := chartMap τ hτ k
  let π := (pullback.fst a b≫a)≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : IsReduced (pullback a b) := isReduced_of_isOpenImmersion (pullback.fst a b)
  letI : LocallyOfFiniteType π := by dsimp [π,a,b]; infer_instance
  have hj : (pullback.fst a b≫PELOriginalOrderChartMorphism318.morphism τ hτ a₀ j)≫
      PELOriginalProperComplexCandidate318.structureMap τ hτ=π := by
    rw [Category.assoc,PELOriginalOrderChartMorphism318.over_complex]
    dsimp [π,a]
    rw [Category.assoc,chart_over_complex_base]
  have hk : (pullback.snd a b≫PELOriginalOrderChartMorphism318.morphism τ hτ a₀ k)≫
      PELOriginalProperComplexCandidate318.structureMap τ hτ=π := by
    rw [Category.assoc,PELOriginalOrderChartMorphism318.over_complex]
    change pullback.snd a b≫Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ k)))=_
    rw [←chart_over_complex_base,←Category.assoc]
    exact congrArg (fun h => h≫PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (pullback.condition (f := a) (g := b)).symm
  apply ReducedComplexPointMorphisms318.ext π (PELOriginalProperComplexCandidate318.structureMap τ hτ) _ _ hj hk
  intro p hp
  have hpj : (p≫pullback.fst a b)≫Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ j)))=𝟙 _ := by
    rw [←chart_over_complex_base,Category.assoc,←Category.assoc (pullback.fst a b)]
    exact hp
  have hpk : (p≫pullback.snd a b)≫Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ k)))=𝟙 _ := by
    rw [←chart_over_complex_base,Category.assoc,←Category.assoc (pullback.snd a b),
      ←pullback.condition]
    exact hp
  obtain ⟨z,hz,hzEq⟩ := PELOriginalFullCandidateSchemePoints318.every_affine_point τ hτ j
    (p≫pullback.fst a b) hpj
  obtain ⟨w,hw,hwEq⟩ := PELOriginalFullCandidateSchemePoints318.every_affine_point τ hτ k
    (p≫pullback.snd a b) hpk
  have he : candidateComplexPoint τ hτ (projection (P τ) z)=
      candidateComplexPoint τ hτ (projection (P τ) w) := by
    rw [←PELOriginalChartSchemePointIdentity318.chart_point τ hτ j z hz,
      ←PELOriginalChartSchemePointIdentity318.chart_point τ hτ k w hw,←hzEq,←hwEq]
    simp only [Category.assoc,pullback.condition_assoc]
  have hq := PELOriginalChartSchemePointIdentity318.candidate_point_injective τ hτ he
  rw [←Category.assoc,←Category.assoc,hzEq,hwEq,
    PELOriginalOrderChartMorphism318.chart_action,PELOriginalOrderChartMorphism318.chart_action,hq]

/-- Genuine algebraic endomorphism of the SAME original candidate for EVERY
element of the entire original half-integral quaternionic order. -/
@[expose] def morphism : candidate τ hτ ⟶
    candidate τ hτ :=
  (cover τ hτ).glueMorphisms (PELOriginalOrderChartMorphism318.morphism τ hτ a₀) (compatible τ hτ a₀)

@[reassoc] theorem chart_morphism (j : Label 3) :
    chartMap τ hτ j≫morphism τ hτ a₀=PELOriginalOrderChartMorphism318.morphism τ hτ a₀ j :=
  (cover τ hτ).ι_glueMorphisms _ _ j

@[reassoc] theorem over_complex :
    morphism τ hτ a₀≫PELOriginalProperComplexCandidate318.structureMap τ hτ=
      PELOriginalProperComplexCandidate318.structureMap τ hτ := by
  apply (cover τ hτ).hom_ext
  intro j
  rw [←Category.assoc,chart_morphism,PELOriginalOrderChartMorphism318.over_complex,
    chart_over_complex_base]

/-- Exact global original source square for all cover representatives. -/
theorem original_point_action (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z)≫morphism τ hτ a₀=
      candidateComplexPoint τ hτ (orderEnd representation order τ a₀ (projection (P τ) z)) := by
  obtain ⟨j,hj⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z
  rw [←PELOriginalChartSchemePointIdentity318.chart_point τ hτ j z hj,
    Category.assoc,chart_morphism]
  exact PELOriginalOrderChartMorphism318.chart_action τ hτ a₀ j z hj
/-- Exact action on the ENTIRE original torus, after the algebraic
morphism has independently been constructed. -/
theorem point_action (q : Base τ) :
    candidateComplexPoint τ hτ q≫morphism τ hτ a₀=
      candidateComplexPoint τ hτ (orderEnd representation order τ a₀ q) := by
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  exact original_point_action τ hτ a₀ z
end PELOriginalOrderSchemeMorphism318
