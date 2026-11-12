module
public import PELOriginalOrderRegularMatrix318
public import RankOneAffinePointAction318
public import ReducedComplexPointMorphisms318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace PELOriginalOrderChartMorphism318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open QuaternionicOrderPeriodQuotient318 PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateNineChartCover318 PELOriginalAllLevelProjectiveMap318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318 PELOriginalComplementaryOrder318
open PELOriginalComplementaryHermitian318 PELOriginalOrderPullbackSections318 PELOriginalOrderRegularMatrix318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFinite : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) := chart_finite_type τ hτ j
local instance structureFiniteType : LocallyOfFiniteType
    (AffineComplexProjectiveVector318.structureMap (A := CoordinateChart τ hτ j)) := by
  dsimp [AffineComplexProjectiveVector318.structureMap]
  infer_instance
local instance standardGrading : GradedAlgebra
    (ComplexProjectiveMarkerPoint318.grading (ι := Label 3)) := MvPolynomial.gradedAlgebra

/-- Actual regular map on the WHOLE chart, produced from genuine
regularized full sections and all-prime rank-one column gluing. -/
@[expose] def ambientMorphism : Spec (CommRingCat.of (CoordinateChart τ hτ j)) ⟶ ambient :=
  RankOneAffineProjectiveMorphism318.morphism (regular τ hτ a j)
    (entry_span τ hτ a j) (minors τ hτ a j)
local instance ambient_quasiCompact : QuasiCompact (ambientMorphism τ hτ a j) := by infer_instance

@[reassoc] theorem ambient_over_complex :
    ambientMorphism τ hτ a j≫ComplexProjectiveBase318.structureMap=
      AffineComplexProjectiveVector318.structureMap (A := CoordinateChart τ hτ j) :=
  RankOneAffineProjectiveMorphism318.over_complex _ _ _

theorem ambient_original_action (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      ambientMorphism τ hτ a j=ambientPoint τ hτ (projection (P τ) (linear a z)) := by
  have hs := RankOneAffinePointAction318.segre_action
    (regular τ hτ a j) (entry_span τ hτ a j) (minors τ hτ a j)
    (algebraEvaluation τ hτ z j hz)
    (fun i => value τ hτ 3 i (linear a z))
    (fun c : Columns => value τ hτ 3 c.1 (linear a z)*
      value τ hτ 3 c.2.1 (linear (complement a) z)*
      value τ hτ 3 c.2.2 (linear (complement a) z)/(value τ hτ 3 j z)^(2*degree a))
    (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ (linear a z))
    (by intro i c; rw [regular_cover]; simp only [entireValue]; ring)
  change _=ComplexProjectiveSchemePoint318.point _ _
  rw [hs]
  apply ComplexProjectivePointEquality318.scheme_point_eq
  exact (original_covering_square τ hτ 1 (linear a z)).symm

lemma all_complex_points_in_candidate
    (p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (CoordinateChart τ hτ j)))
    (hp : p≫AffineComplexProjectiveVector318.structureMap=𝟙 _) :
    ambientMorphism τ hτ a j (p (IsLocalRing.closedPoint ℂ))∈zeroSet τ hτ := by
  obtain ⟨f,rfl⟩ := AffineComplexProjectiveVector318.exists_algebraPoint p hp
  obtain ⟨z,hz,rfl⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  change (Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
    ambientMorphism τ hτ a j) (IsLocalRing.closedPoint ℂ)∈_
  rw [ambient_original_action]
  exact ambientPoint_range τ hτ _ ⟨_,rfl⟩

/-- Full reduced-source radical-kernel factorization into the SAME
candidate, including every scheme prime and the actual structure map. -/
@[expose] def morphism : Spec (CommRingCat.of (CoordinateChart τ hτ j)) ⟶ candidate τ hτ :=
  ReducedComplexPointMorphisms318.factor
    (AffineComplexProjectiveVector318.structureMap (A := CoordinateChart τ hτ j))
    (ambientMorphism τ hτ a j) (zeroSet τ hτ) (all_complex_points_in_candidate τ hτ a j)
@[reassoc] theorem inclusion_square :
    morphism τ hτ a j≫inclusion τ hτ=ambientMorphism τ hτ a j :=
  ReducedComplexPointMorphisms318.factor_inclusion _ _ _ _
@[reassoc] theorem over_complex :
    morphism τ hτ a j≫PELOriginalProperComplexCandidate318.structureMap τ hτ=
      AffineComplexProjectiveVector318.structureMap (A := CoordinateChart τ hτ j) := by
  change morphism τ hτ a j≫(inclusion τ hτ≫ComplexProjectiveBase318.structureMap)=_
  rw [←Category.assoc,inclusion_square,ambient_over_complex]

theorem chart_action (z : ComplexVectors) (hz : value τ hτ 3 j z≠0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      morphism τ hτ a j=
      candidateComplexPoint τ hτ (orderEnd representation order τ a (projection (P τ) z)) := by
  apply (cancel_mono (inclusion τ hτ)).mp
  rw [Category.assoc,inclusion_square,candidateComplexPoint_inclusion,ambient_original_action]
  rfl
end PELOriginalOrderChartMorphism318
