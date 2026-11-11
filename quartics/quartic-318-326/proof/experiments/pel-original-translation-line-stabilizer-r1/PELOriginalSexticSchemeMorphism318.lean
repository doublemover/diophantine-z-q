module
public import PELOriginalSexticSchemePoint318
public import ReducedComplexPointMorphisms318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace PELOriginalSexticSchemeMorphism318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0<τ.im)
local instance standardGrading : GradedAlgebra (ComplexProjectiveMarkerPoint318.grading (ι := Label 6)) :=
  MvPolynomial.gradedAlgebra

/-- Agreement on the ACTUAL scheme pullback of any two original cubic
charts. Reducedness comes from the actual open immersion, and the
finite-type/separated point criterion is used only after every C-valued
point is computed by its true original source representative. -/
theorem compatible (j k : Label 3) :
    pullback.fst (chartMap τ hτ j) (chartMap τ hτ k)≫
      PELOriginalSexticChartMorphism318.morphism τ hτ j=
    pullback.snd (chartMap τ hτ j) (chartMap τ hτ k)≫
      PELOriginalSexticChartMorphism318.morphism τ hτ k := by
  let a := chartMap τ hτ j
  let b := chartMap τ hτ k
  let π := (pullback.fst a b≫a)≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : IsReduced (pullback a b) := isReduced_of_isOpenImmersion (pullback.fst a b)
  letI : LocallyOfFiniteType π := by dsimp [π,a,b]; infer_instance
  have hj : (pullback.fst a b≫PELOriginalSexticChartMorphism318.morphism τ hτ j)≫
      ComplexProjectiveBase318.structureMap=π := by
    rw [Category.assoc,PELOriginalSexticChartMorphism318.over_complex]
    dsimp [π,a]
    rw [Category.assoc,chart_over_complex_base]
  have hk : (pullback.snd a b≫PELOriginalSexticChartMorphism318.morphism τ hτ k)≫
      ComplexProjectiveBase318.structureMap=π := by
    rw [Category.assoc,PELOriginalSexticChartMorphism318.over_complex]
    change pullback.snd a b≫Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (CoordinateChart τ hτ k)))=_
    rw [←chart_over_complex_base,←Category.assoc]
    exact congrArg (fun h => h≫PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (pullback.condition (f := a) (g := b)).symm
  apply ReducedComplexPointMorphisms318.ext π ComplexProjectiveBase318.structureMap _ _ hj hk
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
    PELOriginalSexticSchemePoint318.chart_action,PELOriginalSexticSchemePoint318.chart_action,hq]

/-- A genuine GLOBAL regular morphism of the SAME original algebraic
candidate to level-six projective scheme space. No GAGA, normal
generation, or transported analytic group law is used to glue it. -/
@[expose] def morphism : candidate τ hτ ⟶
    Proj (ComplexProjectiveMarkerPoint318.grading (ι := Label 6)) :=
  (cover τ hτ).glueMorphisms (PELOriginalSexticChartMorphism318.morphism τ hτ) (compatible τ hτ)

@[reassoc] theorem chart_morphism (j : Label 3) :
    chartMap τ hτ j≫morphism τ hτ=PELOriginalSexticChartMorphism318.morphism τ hτ j :=
  (cover τ hτ).ι_glueMorphisms _ _ j

@[reassoc] theorem over_complex :
    morphism τ hτ≫ComplexProjectiveBase318.structureMap=
      PELOriginalProperComplexCandidate318.structureMap τ hτ := by
  apply (cover τ hτ).hom_ext
  intro j
  rw [←Category.assoc,chart_morphism,PELOriginalSexticChartMorphism318.over_complex,
    chart_over_complex_base]

/-- Exact global original source square for all cover representatives. -/
theorem original_point_action (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z)≫morphism τ hτ=
      PELOriginalSexticSchemePoint318.point τ hτ (projection (P τ) z) := by
  obtain ⟨j,hj⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z
  rw [←PELOriginalChartSchemePointIdentity318.chart_point τ hτ j z hj,
    Category.assoc,chart_morphism]
  exact PELOriginalSexticSchemePoint318.chart_action τ hτ j z hj
end PELOriginalSexticSchemeMorphism318
