module
public import ActualOriginalCanonicalOverlapLength318
public section
noncomputable section
namespace ActualOriginalCanonicalSliceBudget318
open QuadricCRTAssembly318 ActualOriginalCanonicalSupportBox318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalWeightedWeylBound318
open ActualOriginalBoxOverlap318 ActualOriginalBoxSliceAggregation318
open ActualOriginalCompactCircleCount318 ActualOriginalScaledCircle318
open scoped BigOperators

/-- The exact sum of absolute first-coordinate slices, on all original
box displacements and all FOUR outer overlap coordinates. -/
@[expose] def canonicalSliceBudget (κ : ℤ) (H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) : ℝ :=
  ∑ h ∈ differences (centeredBox H),
    ∑ b ∈ overlap (Finset.Icc (-H) H) h.1.2,
    ∑ c ∈ overlap (Finset.Icc (-H) H) h.2.1.1,
    ∑ d ∈ overlap (Finset.Icc (-H) H) h.2.1.2,
    ∑ e ∈ overlap (Finset.Icc (-H) H) h.2.2,
      ‖sliceCorrelation κ w θ h (overlap (Finset.Icc (-H) H) h.1.1) b c d e‖

lemma actual_correlation_le_canonical_slices (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) :
    (∑ h ∈ differences (centeredBox H), ‖linearCorrelation κ (centeredBox H) w θ h‖)≤
      canonicalSliceBudget κ H w θ := by
  apply Finset.sum_le_sum
  intro h hh
  exact actual_box_correlation_slice_bound κ w θ h _ _ _ _ _

/-- The actual full original scaled circle sum is bounded on the
canonical compact-support box by its complete constructed slice budget. -/
theorem actual_scaled_circle_canonical_bound (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (R B : ℝ) (hB : 0<B) (hR : ∀ x, W x≠0 → ‖x‖≤R) (θ : ℝ) :
    ‖scaledCircleSum κ θ B W‖^2≤canonicalSliceBudget κ ⌈R*B⌉ (latticeWeight B W)
      (θ : AddCircle (1 : ℝ)) := by
  rw [actual_circle_eq_finite κ B W (centeredBox ⌈R*B⌉)
    (actual_scaled_support_box W R B hB hR)]
  exact (actual_original_weyl_square_bound κ _ _ _).trans
    (actual_correlation_le_canonical_slices κ _ _ _)

/-- Compact support produces one radius for all scales and circle
frequencies. No external finite-support or slice-cover assumption remains. -/
theorem actual_compact_circle_slice_budget (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hc : HasCompactSupport W) :
    ∃ R : ℝ, 1≤R ∧ ∀ B : ℝ, 0<B → ∀ θ : ℝ,
      ‖scaledCircleSum κ θ B W‖^2≤canonicalSliceBudget κ ⌈R*B⌉ (latticeWeight B W)
        (θ : AddCircle (1 : ℝ)) := by
  obtain ⟨R,hR,hs⟩ := actual_compact_support_radius W hc
  exact ⟨R,hR,fun B hB θ => actual_scaled_circle_canonical_bound κ W R B hB hs θ⟩

end ActualOriginalCanonicalSliceBudget318
