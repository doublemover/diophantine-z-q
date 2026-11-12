module
public import ActualOriginalSmoothTwoAxisCancellation318
public section
noncomputable section
namespace ActualOriginalBoxPlaneAggregation318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalBoxOverlap318
open ActualOriginalBoxSliceAggregation318 ActualOriginalCanonicalSupportBox318
open ActualOriginalTwoAxisSliceIdentity318 ActualOriginalCanonicalOverlapLength318
open scoped BigOperators

@[expose] def overlapPlaneCorrelation (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (c d e : ℤ) : ℂ :=
  ∑ b∈overlap (Finset.Icc (-H) H) h.1.2,
    sliceCorrelation κ w θ h (overlap (Finset.Icc (-H) H) h.1.1) b c d e

/-- Cancellation in the first TWO directions occurs before any triangle
inequality. All three remaining overlap coordinates are retained. -/
theorem actual_box_correlation_planes (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) :
    linearCorrelation κ (centeredBox H) w θ h=
      ∑ c∈overlap (Finset.Icc (-H) H) h.2.1.1,
      ∑ d∈overlap (Finset.Icc (-H) H) h.2.1.2,
      ∑ e∈overlap (Finset.Icc (-H) H) h.2.2,
        overlapPlaneCorrelation κ H w θ h c d e := by
  rw [actual_box_correlation_slices]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  rfl

lemma actual_overlap_plane_identity (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (c d e : ℤ) :
    overlapPlaneCorrelation κ H w θ h c d e=
      originalPlaneCorrelation κ w θ h (max (-H) (-H-h.1.1))
        (max (-H) (-H-h.1.2)) c d e (overlapLength H h.1.1) (overlapLength H h.1.2) := by
  unfold overlapPlaneCorrelation
  rw [actual_interval_overlap,actual_interval_overlap,actual_original_two_axis_slice_identity]
  rfl

@[expose] def canonicalPlaneBudget (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) : ℝ :=
  ∑ h∈differences (centeredBox H),
    ∑ c∈overlap (Finset.Icc (-H) H) h.2.1.1,
    ∑ d∈overlap (Finset.Icc (-H) H) h.2.1.2,
    ∑ e∈overlap (Finset.Icc (-H) H) h.2.2,
      ‖overlapPlaneCorrelation κ H w θ h c d e‖

lemma actual_correlation_le_canonical_planes (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) :
    (∑ h∈differences (centeredBox H), ‖linearCorrelation κ (centeredBox H) w θ h‖)≤
      canonicalPlaneBudget κ H w θ := by
  apply Finset.sum_le_sum
  intro h hh
  rw [actual_box_correlation_planes]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  exact norm_sum_le _ _

end ActualOriginalBoxPlaneAggregation318
