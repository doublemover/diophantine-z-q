module
public import ActualOriginalDisplacementBoxKernel318
public section
noncomputable section
namespace ActualOriginalCompleteTwoAxisWeyl318
open QuadricCRTAssembly318 ActualOriginalFiniteCircleIdentity318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalWeightedWeylBound318
open ActualOriginalCanonicalSupportBox318 ActualOriginalBoxPlaneAggregation318
open ActualOriginalPlaneOuterMultiplicity318 ActualOriginalDisplacementBoxKernel318
open ActualOriginalRationalBlockReciprocalSum318 ActualOriginalWeightedBlockReciprocalBudget318
open scoped BigOperators

@[expose] def completeEvenKernel (H : ℤ) (N t : ℝ) : ℝ :=
  ∑ a∈Finset.Icc (-2*H) (2*H), fourierChordCap N (2*a) t
lemma actual_complete_even_kernel_nonneg (H : ℤ) (N t : ℝ) (hN : 0≤N) :
    0≤completeEvenKernel H N t :=
  Finset.sum_nonneg (fun a ha => actual_chord_cap_nonneg N (2*a) t hN)

/-- Complete actual finite Weyl bound. THREE outer overlap coordinates
and THREE outer displacement coordinates each retain their full cube.
Only the two proven cancellation directions contribute kernel factors. -/
theorem actual_complete_two_axis_weyl (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (t N C : ℝ) (hH : 0≤H) (hN : 0≤N) (hC : 0≤C)
    (hb : ∀ h c d e,
      ‖overlapPlaneCorrelation κ H w (t : AddCircle (1 : ℝ)) h c d e‖≤
        fourierChordCap N (2*h.1.1) t*fourierChordCap N (2*h.1.2) t*C) :
    ‖originalCircleSum κ (centeredBox H) w (t : AddCircle (1 : ℝ))‖^2≤
      (2*(H : ℝ)+1)^3*(4*(H : ℝ)+1)^3*C*(completeEvenKernel H N t)^2 := by
  have hN0 : (0 : ℝ)≤2*(H : ℝ)+1 := by exact_mod_cast (show (0 : ℤ)≤2*H+1 by omega)
  have hmajor := actual_canonical_plane_outer_budget κ H w (t : AddCircle (1 : ℝ)) hH
    (fun h => fourierChordCap N (2*h.1.1) t*fourierChordCap N (2*h.1.2) t*C)
    (fun h => mul_nonneg (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN)
      (actual_chord_cap_nonneg _ _ _ hN)) hC) hb
  have hkernel := actual_complete_two_axis_kernel H hH
    (fun a => fourierChordCap N (2*a) t) (fun b => fourierChordCap N (2*b) t)
    (fun a => actual_chord_cap_nonneg _ _ _ hN) (fun b => actual_chord_cap_nonneg _ _ _ hN)
  calc
    _ ≤ ∑ h∈differences (centeredBox H),
        ‖linearCorrelation κ (centeredBox H) w (t : AddCircle (1 : ℝ)) h‖ :=
      actual_original_weyl_square_bound κ _ _ _
    _ ≤ canonicalPlaneBudget κ H w (t : AddCircle (1 : ℝ)) :=
      actual_correlation_le_canonical_planes κ H w _
    _ ≤ (2*(H : ℝ)+1)^3*((∑ h∈differences (centeredBox H),
        fourierChordCap N (2*h.1.1) t*fourierChordCap N (2*h.1.2) t)*C) := by
      simpa only [Finset.sum_mul] using hmajor
    _ ≤ (2*(H : ℝ)+1)^3*
        (((4*(H : ℝ)+1)^3*completeEvenKernel H N t*completeEvenKernel H N t)*C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkernel hC) (pow_nonneg hN0 3)
    _ = _ := by ring

end ActualOriginalCompleteTwoAxisWeyl318
