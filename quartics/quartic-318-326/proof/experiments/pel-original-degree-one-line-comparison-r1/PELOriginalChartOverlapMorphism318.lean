module
public import PELOriginalOverlapEvaluation318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace PELOriginalChartOverlapMorphism318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartOverlapLocalization318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateChartBase318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) := chart_integral_domain τ hτ j
local instance chartFinite : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) := chart_finite_type τ hτ j
local instance overlapFinite : Algebra.FiniteType ℂ (Overlap τ hτ j k) := by infer_instance
local instance overlapReduced : IsReduced (Spec (CommRingCat.of (Overlap τ hτ j k))) := by
  infer_instance
local instance overlapLFT : LocallyOfFiniteType
    (AffineComplexProjectiveVector318.structureMap (A := Overlap τ hτ j k)) := by
  dsimp [AffineComplexProjectiveVector318.structureMap]
  infer_instance

@[expose] def left : Spec (CommRingCat.of (Overlap τ hτ j k)) ⟶
    Spec (CommRingCat.of (CoordinateChart τ hτ j)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ (Overlap τ hτ j k)))
@[expose] def right : Spec (CommRingCat.of (Overlap τ hτ j k)) ⟶
    Spec (CommRingCat.of (CoordinateChart τ hτ k)) :=
  Spec.map (CommRingCat.ofHom (fromOther τ hτ j k).toRingHom)

/-- The full ring map constructed independently from literal homogeneous
ratios is the geometric overlap map for the SAME original candidate.
Reducedness and finite type justify full morphism ext; the point-level
input supplies both whole-ring evaluations of one original lift. -/
theorem square : left τ hτ j k ≫ chartMap τ hτ j =
    right τ hτ j k ≫ chartMap τ hτ k := by
  apply ReducedComplexPointMorphisms318.ext
    (AffineComplexProjectiveVector318.structureMap (A := Overlap τ hτ j k))
    (PELOriginalProperComplexCandidate318.structureMap τ hτ)
  · rw [Category.assoc,chart_over_complex_base,left,←Spec.map_comp]
    congr 1
    ext c
    exact (IsScalarTower.algebraMap_apply ℂ (CoordinateChart τ hτ j)
      (Overlap τ hτ j k) c).symm
  · rw [Category.assoc,chart_over_complex_base,right,←Spec.map_comp]
    congr 1
    ext c
    exact (fromOther τ hτ j k).commutes c
  intro p hp
  obtain ⟨f,rfl⟩ := AffineComplexProjectiveVector318.exists_algebraPoint p hp
  obtain ⟨z,hj,hk,hfj,hfk⟩ := PELOriginalOverlapEvaluation318.original_evaluations τ hτ j k f
  have hl : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ left τ hτ j k =
      Spec.map (CommRingCat.ofHom
        (PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z j hj).toRingHom) := by
    rw [left,←Spec.map_comp]
    congr 1
    ext a
    exact hfj a
  have hr : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ right τ hτ j k =
      Spec.map (CommRingCat.ofHom
        (PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z k hk).toRingHom) := by
    rw [right,←Spec.map_comp]
    congr 1
    ext a
    exact congrArg (fun g : CoordinateChart τ hτ k →ₐ[ℂ] ℂ => g a) hfk
  rw [←Category.assoc,hl,PELOriginalChartSchemePointIdentity318.chart_point,
    ←Category.assoc,hr,PELOriginalChartSchemePointIdentity318.chart_point]

instance left_open : IsOpenImmersion (left τ hτ j k) := by
  dsimp [left]
  infer_instance

lemma chart_range (i : Label 3) :
    (chartMap τ hτ i).opensRange = candidateChart τ hτ i := by
  ext x
  change (∃ y, chartMap τ hτ i y = x) ↔ x ∈ candidateChart τ hτ i
  constructor
  · rintro ⟨y,rfl⟩
    exact ((actualChartIso τ hτ i).hom y).property
  · intro hx
    refine ⟨(actualChartIso τ hτ i).inv ⟨x,hx⟩,?_⟩
    exact congrArg (candidateChart τ hτ i).ι
      (Iso.inv_hom_id_apply (actualChartIso τ hτ i) ⟨x,hx⟩)

/-- The literal localization ring and its independently constructed
opposite-chart homomorphism form the actual scheme pullback, including
all sheaf and infinitesimal data. -/
theorem cartesian : CategoryTheory.Limits.IsPullback
    (right τ hτ j k) (left τ hτ j k) (chartMap τ hτ k) (chartMap τ hτ j) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (square τ hτ j k)
  rw [chart_range,PELOriginalChartIntersectionOpen318.preimage_chart]
  apply TopologicalSpace.Opens.ext
  exact (PrimeSpectrum.localization_away_comap_range _ _).symm

instance right_open : IsOpenImmersion (right τ hτ j k) :=
  MorphismProperty.of_isPullback (cartesian τ hτ j k).flip
    (inferInstance : IsOpenImmersion (chartMap τ hτ j))
end PELOriginalChartOverlapMorphism318
