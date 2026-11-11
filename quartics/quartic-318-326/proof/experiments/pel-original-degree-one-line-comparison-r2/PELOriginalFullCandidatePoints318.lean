module
public import PELOriginalFullAffineCandidateImage318
public import PELOriginalProjectiveImageFromAffine318
public section
noncomputable section
namespace PELOriginalFullCandidatePoints318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineOpenImage318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalClosedAffineImage318
open ComplexProjectiveComplexAtlas318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

lemma pointVector_original (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    pointVector τ hτ j (algebraEvaluation τ hτ z j hz) = ratioVector τ hτ 1 j z := by
  change coordinates (Label 3) 0 j (fun i =>
    algebraEvaluation τ hτ z j hz (ratioElement τ hτ j i.val)) = _
  have hr : (fun i : {i : Label 3 // i ≠ j} =>
      algebraEvaluation τ hτ z j hz (ratioElement τ hτ j i.val)) =
      (fun i : {i : Label 3 // i ≠ j} => value τ hτ 3 i.val z / value τ hτ 3 j z) := by
    funext i
    exact actual_ratio_evaluation τ hτ z j i.val hz
  rw [hr]
  rfl

lemma original_subset_candidate : affineImage τ hτ j ⊆ candidateLocus τ hτ j := by
  rintro w ⟨z,hz,rfl⟩
  rw [←pointVector_original τ hτ j z hz]
  exact pointVector_mem τ hτ j (algebraEvaluation τ hτ z j hz)

/-- Full equality of the independent candidate affine locus and the
original theta image, with no common-open restriction. -/
theorem affine_equality : candidateLocus τ hτ j = affineImage τ hτ j :=
  Set.Subset.antisymm
    (PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ j)
    (original_subset_candidate τ hτ j)

/-- EVERY ordinary complex point of the WHOLE original chart equals
an actual theta evaluation on ALL chart elements. No denominator,
genericity, smoothness, selected component or chosen sheet is assumed. -/
theorem every_chart_point (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ) :
    ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
      f = algebraEvaluation τ hτ z j hz := by
  have hw := (PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ j)
    (pointVector_mem τ hτ j f)
  obtain ⟨z,hz,hcoord⟩ := hw
  refine ⟨z,hz,?_⟩
  apply (equivalence τ hτ j).injective
  apply Subtype.ext
  change pointVector τ hτ j f = pointVector τ hτ j (algebraEvaluation τ hτ z j hz)
  rw [pointVector_original,hcoord]

/-- The ENTIRE projective relation locus equals the original compact
projective theta image, including every point outside the primitive
common open and every original coordinate-chart boundary. -/
theorem projective_equality : PELOriginalProjectiveImageFromAffine318.projectiveLocus τ hτ =
    PELOriginalLevelThreeClosedEmbedding318.image τ hτ :=
  PELOriginalProjectiveImageFromAffine318.equality_of_affine τ hτ
    (PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ)
end PELOriginalFullCandidatePoints318
