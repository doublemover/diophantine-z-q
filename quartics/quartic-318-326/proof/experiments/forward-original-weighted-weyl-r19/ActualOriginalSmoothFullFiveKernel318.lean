module
public import ActualOriginalFiveKernelSumBound318
public section
noncomputable section
namespace ActualOriginalSmoothFullFiveKernel318
open QuadricCRTAssembly318 ActualOriginalFiniteCircleIdentity318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalWeightedWeylBound318
open ActualOriginalCompactCircleCount318 ActualOriginalScaledCircle318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalDisplacementBoxKernel318 ActualOriginalFiveKernelCorrelation318
open ActualOriginalFiveKernelSumBound318
open scoped ContDiff BigOperators

/-- Full ORIGINAL smooth compact five-variable sum, with all five
correlation directions cancelled and every displacement counted. There
are NO residual overlap/displacement cardinality cubes. -/
theorem actual_smooth_complete_five_kernel (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ t : ℝ,
      ‖scaledCircleSum κ t B W‖^2≤
        C*(2*R+4)^5*completeFiveKernel κ ⌈R*B⌉ (2*(⌈R*B⌉ : ℝ)+1) t := by
  obtain ⟨R,hR,hs⟩ := actual_compact_support_radius W hc
  obtain ⟨C,hC,hcorr⟩ := actual_smooth_five_kernel_correlation κ W hW hc
  refine ⟨R,C,hR,hC,fun B hB t => ?_⟩
  have hB0 : 0<B := by linarith
  have hH := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have hHr : (0 : ℝ)≤(⌈R*B⌉ : ℝ) := by exact_mod_cast hH
  have hsize : 2*(⌈R*B⌉ : ℝ)+1≤(2*R+3)*B := by
    have hh := Int.ceil_lt_add_one (R*B)
    nlinarith
  have hK : 0≤C*(1+(2*R+3))^5 := mul_nonneg hC (pow_nonneg (by linarith) _)
  rw [actual_circle_eq_finite κ B W (centeredBox ⌈R*B⌉)
    (actual_scaled_support_box W R B hB0 hs)]
  calc
    _ ≤ ∑ h∈differences (centeredBox ⌈R*B⌉),
        ‖linearCorrelation κ (centeredBox ⌈R*B⌉) (latticeWeight B W) (t : AddCircle (1 : ℝ)) h‖ :=
      actual_original_weyl_square_bound κ _ _ _
    _ ≤ ∑ h∈differences (centeredBox ⌈R*B⌉),
        C*(1+(2*R+3))^5*fiveChordProduct κ (2*(⌈R*B⌉ : ℝ)+1) t h := by
      apply Finset.sum_le_sum
      intro h hh
      exact hcorr B (2*R+3) hB0 (by linarith) ⌈R*B⌉ hH hsize h
        (actual_original_displacements_subset ⌈R*B⌉ hh) t
    _ = C*(1+(2*R+3))^5*(∑ h∈differences (centeredBox ⌈R*B⌉),
        fiveChordProduct κ (2*(⌈R*B⌉ : ℝ)+1) t h) := by rw [Finset.mul_sum]
    _ ≤ C*(1+(2*R+3))^5*completeFiveKernel κ ⌈R*B⌉ (2*(⌈R*B⌉ : ℝ)+1) t :=
      mul_le_mul_of_nonneg_left (actual_five_kernel_sum κ ⌈R*B⌉ _ t (by positivity)) hK
    _ = _ := by ring

end ActualOriginalSmoothFullFiveKernel318
