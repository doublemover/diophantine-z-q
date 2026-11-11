module
public import RankOneAffinePointAction318
public import PELOriginalAdditionCandidateRelations318
public import PELOriginalChartSchemePointIdentity318
public import ReducedComplexPointMorphisms318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace PELOriginalAdditionChartMorphism318
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalAllLevelProjectiveMap318
open PELOriginalPolarizationTransitions318 PELOriginalProductChartPoints318
open PELOriginalRegularAdditionTensor318 PELOriginalAdditionBasepointFree318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
variable (τ : ℂ) (hτ : 0<τ.im) (j k : Label 3)
local instance productStructureFiniteType : LocallyOfFiniteType
    (AffineComplexProjectiveVector318.structureMap (A := ProductRing τ hτ j k)) := by
  dsimp [AffineComplexProjectiveVector318.structureMap]
  infer_instance

/-- Actual regular ambient addition map from the ENTIRE product chart.
The genuine81 entry ideal and full rank-one equations supply all
principal-open column maps and their scheme gluing. -/
@[expose] def ambientMorphism : Spec (CommRingCat.of (ProductRing τ hτ j k)) ⟶ ambient :=
  RankOneAffineProjectiveMorphism318.morphism (fun r s => coordinate τ hτ j k (r,s))
    (span_eq_top τ hτ j k) (rank_one τ hτ j k)

local instance ambient_quasiCompact : QuasiCompact (ambientMorphism τ hτ j k) := by
  infer_instance

@[reassoc] theorem ambient_over_complex :
    ambientMorphism τ hτ j k≫ComplexProjectiveBase318.structureMap=
      AffineComplexProjectiveVector318.structureMap (A := ProductRing τ hτ j k) :=
  RankOneAffineProjectiveMorphism318.over_complex _ _ _

/-- Exact literal sum z+a on actual original pair evaluations. The
second factor and common denominator remain present until the valid
nonzero Segre column is selected; no addition formula is inferred from
point equality alone. -/
theorem ambient_original_action (z a : ComplexVectors)
    (hz : value τ hτ 3 j z≠0) (ha : value τ hτ 3 k a≠0) :
    Spec.map (CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
      (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom)≫
      ambientMorphism τ hτ j k=ambientPoint τ hτ (projection (P τ) (z+a)) := by
  have hs := RankOneAffinePointAction318.segre_action
    (fun r s => coordinate τ hτ j k (r,s)) (span_eq_top τ hτ j k) (rank_one τ hτ j k)
    (TensorComplexPointSeparation318.evaluation (algebraEvaluation τ hτ z j hz)
      (algebraEvaluation τ hτ a k ha))
    (fun r => value τ hτ 3 r (z+a))
    (fun s => value τ hτ 3 s (z-a)/((value τ hτ 3 j z)^2*(value τ hτ 3 k a)^2))
    (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ (z+a))
    (by intro r s; rw [evaluation]; ring)
  change _=ComplexProjectiveSchemePoint318.point _ _
  rw [hs]
  apply ComplexProjectivePointEquality318.scheme_point_eq
  exact (original_covering_square τ hτ 1 (z+a)).symm

lemma all_complex_points_in_candidate
    (p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (ProductRing τ hτ j k)))
    (hp : p≫AffineComplexProjectiveVector318.structureMap=𝟙 _) :
    ambientMorphism τ hτ j k (p (IsLocalRing.closedPoint ℂ))∈zeroSet τ hτ := by
  obtain ⟨f,rfl⟩ := AffineComplexProjectiveVector318.exists_algebraPoint p hp
  rw [point_factorization τ hτ j k f]
  obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j
    (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨a,ha,hg⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k
    (f.comp Algebra.TensorProduct.includeRight)
  rw [hf,hg]
  change (Spec.map (CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
    (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom)≫
      ambientMorphism τ hτ j k) (IsLocalRing.closedPoint ℂ)∈_
  rw [ambient_original_action]
  exact ambientPoint_range τ hτ _ ⟨_,rfl⟩

/-- Genuine morphism to the SAME reduced original candidate. The source
is the actual product tensor ring, proved reduced; Jacobson closed-point
density and the radical kernel factorization preserve all scheme primes
and structure sheaves, not only original complex pairs. -/
@[expose] def morphism : Spec (CommRingCat.of (ProductRing τ hτ j k)) ⟶ candidate τ hτ :=
  ReducedComplexPointMorphisms318.factor
    (AffineComplexProjectiveVector318.structureMap (A := ProductRing τ hτ j k))
    (ambientMorphism τ hτ j k) (zeroSet τ hτ) (all_complex_points_in_candidate τ hτ j k)

@[reassoc] theorem inclusion_square :
    morphism τ hτ j k≫inclusion τ hτ=ambientMorphism τ hτ j k :=
  ReducedComplexPointMorphisms318.factor_inclusion _ _ _ _

@[reassoc] theorem over_complex :
    morphism τ hτ j k≫PELOriginalProperComplexCandidate318.structureMap τ hτ=
      AffineComplexProjectiveVector318.structureMap (A := ProductRing τ hτ j k) := by
  change morphism τ hτ j k≫(inclusion τ hτ≫ComplexProjectiveBase318.structureMap)=_
  rw [←Category.assoc,inclusion_square,ambient_over_complex]

/-- Literal original group addition at EVERY original pair in this
whole product chart, as equality of actual candidate Spec(C) morphisms. -/
theorem original_point_action (z a : ComplexVectors)
    (hz : value τ hτ 3 j z≠0) (ha : value τ hτ 3 k a≠0) :
    Spec.map (CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
      (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom)≫
      morphism τ hτ j k=candidateComplexPoint τ hτ (projection (P τ) (z+a)) := by
  apply (cancel_mono (inclusion τ hτ)).mp
  rw [Category.assoc,inclusion_square,candidateComplexPoint_inclusion,ambient_original_action]

/-- Every actual over-C tensor-chart point is a literal original pair
with BOTH original cubic denominators nonzero. -/
theorem every_point
    (p : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (ProductRing τ hτ j k)))
    (hp : p≫AffineComplexProjectiveVector318.structureMap=𝟙 _) :
    ∃ z a : ComplexVectors, ∃ hz : value τ hτ 3 j z≠0, ∃ ha : value τ hτ 3 k a≠0,
      p=Spec.map (CommRingCat.ofHom (TensorComplexPointSeparation318.evaluation
        (algebraEvaluation τ hτ z j hz) (algebraEvaluation τ hτ a k ha)).toRingHom) := by
  obtain ⟨f,rfl⟩ := AffineComplexProjectiveVector318.exists_algebraPoint p hp
  obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j
    (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨a,ha,hg⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ k
    (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨z,a,hz,ha,?_⟩
  rw [point_factorization τ hτ j k f,hf,hg]
end PELOriginalAdditionChartMorphism318
