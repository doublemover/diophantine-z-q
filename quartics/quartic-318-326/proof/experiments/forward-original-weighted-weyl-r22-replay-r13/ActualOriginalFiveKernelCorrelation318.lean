module
public import ActualOriginalPositiveOverlapRectangle318
public section
noncomputable section
namespace ActualOriginalFiveKernelCorrelation318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCanonicalSupportBox318
open ActualOriginalCompactCircleCount318 ActualOriginalPositiveOverlapRectangle318
open ActualOriginalFiveAxisCancellation318 ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalWeightedBlockReciprocalBudget318 ActualOriginalSmoothOverlapPlane318
open scoped ContDiff

@[expose] def fiveChordProduct (κ : ℤ) (N t : ℝ) (h : Coordinates ℤ) : ℝ :=
  fourierChordCap N (2*h.1.1) t*fourierChordCap N (2*h.1.2) t*
    fourierChordCap N (2*(-h.2.1.1)) t*fourierChordCap N (2*(-h.2.1.2)) t*
    fourierChordCap N (2*(-(κ*h.2.2))) t
lemma actual_five_chord_nonneg (κ : ℤ) (N t : ℝ) (hN : 0≤N) (h : Coordinates ℤ) :
    0≤fiveChordProduct κ N t h := by
  unfold fiveChordProduct
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (actual_chord_cap_nonneg _ _ _ hN) (actual_chord_cap_nonneg _ _ _ hN))
    (actual_chord_cap_nonneg _ _ _ hN)) (actual_chord_cap_nonneg _ _ _ hN))
    (actual_chord_cap_nonneg _ _ _ hN)

lemma actual_five_caps_common_length (κ : ℤ) (t N : ℝ) (hN : 0≤N)
    (h : Coordinates ℤ) (n₀ n₁ n₂ n₃ n₄ : ℝ)
    (hn₀ : 0≤n₀) (hn₁ : 0≤n₁) (hn₂ : 0≤n₂) (hn₃ : 0≤n₃) (hn₄ : 0≤n₄)
    (h₀ : n₀≤N) (h₁ : n₁≤N) (h₂ : n₂≤N) (h₃ : n₃≤N) (h₄ : n₄≤N) :
    fourierChordCap n₀ (2*h.1.1) t*fourierChordCap n₁ (2*h.1.2) t*
      fourierChordCap n₂ (2*(-h.2.1.1)) t*fourierChordCap n₃ (2*(-h.2.1.2)) t*
      fourierChordCap n₄ (2*(-(κ*h.2.2))) t≤fiveChordProduct κ N t h := by
  have h01 := mul_le_mul (actual_chord_cap_mono _ _ _ _ h₀) (actual_chord_cap_mono _ _ _ _ h₁)
    (actual_chord_cap_nonneg n₁ (2*h.1.2) t hn₁) (actual_chord_cap_nonneg N (2*h.1.1) t hN)
  have h012 := mul_le_mul h01 (actual_chord_cap_mono _ _ (2*(-h.2.1.1)) t h₂)
    (actual_chord_cap_nonneg _ _ _ hn₂)
    (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN) (actual_chord_cap_nonneg _ _ _ hN))
  have h0123 := mul_le_mul h012 (actual_chord_cap_mono _ _ (2*(-h.2.1.2)) t h₃)
    (actual_chord_cap_nonneg _ _ _ hn₃)
    (mul_nonneg (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN)
      (actual_chord_cap_nonneg _ _ _ hN)) (actual_chord_cap_nonneg _ _ _ hN))
  exact mul_le_mul h0123 (actual_chord_cap_mono _ _ (2*(-(κ*h.2.2))) t h₄)
    (actual_chord_cap_nonneg _ _ _ hn₄)
    (mul_nonneg (mul_nonneg (mul_nonneg (actual_chord_cap_nonneg _ _ _ hN)
      (actual_chord_cap_nonneg _ _ _ hN)) (actual_chord_cap_nonneg _ _ _ hN))
      (actual_chord_cap_nonneg _ _ _ hN))

/-- Every actual five-dimensional overlap correlation has FIVE kernel
factors, with no outer overlap coordinate paid trivially or omitted. -/
theorem actual_smooth_five_kernel_correlation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B R : ℝ, 0<B → 0≤R → ∀ H : ℤ, 0≤H →
      2*(H : ℝ)+1≤R*B → ∀ h∈centeredBox (2*H), ∀ t : ℝ,
      ‖linearCorrelation κ (centeredBox H) (latticeWeight B W) (t : AddCircle (1 : ℝ)) h‖≤
        C*(1+R)^5*fiveChordProduct κ (2*(H : ℝ)+1) t h := by
  obtain ⟨C,hC,hb⟩ := actual_smooth_five_axis_cancellation κ W hW hc
  refine ⟨C,hC,fun B R hB hR H hH hsize h hh t => ?_⟩
  have hc' := hh
  simp only [centeredBox,originalBox,Finset.mem_product] at hc'
  have h₀ := actual_overlap_steps_le H h.1.1 hH hc'.1.1
  have h₁ := actual_overlap_steps_le H h.1.2 hH hc'.1.2
  have h₂ := actual_overlap_steps_le H h.2.1.1 hH hc'.2.1.1
  have h₃ := actual_overlap_steps_le H h.2.1.2 hH hc'.2.1.2
  have h₄ := actual_overlap_steps_le H h.2.2 hH hc'.2.2
  rw [actual_correlation_five_rectangle κ H B W _ h hH hh]
  apply (hb B R hB hR h (overlapCorner H h) _ _ _ _ _
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) t).trans
  apply mul_le_mul_of_nonneg_left
  · exact actual_five_caps_common_length κ t (2*(H : ℝ)+1)
      (by have : (0 : ℝ)≤H := by exact_mod_cast hH; linarith) h _ _ _ _ _
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) h₀ h₁ h₂ h₃ h₄
  · exact mul_nonneg hC (pow_nonneg (by linarith) _)

end ActualOriginalFiveKernelCorrelation318
