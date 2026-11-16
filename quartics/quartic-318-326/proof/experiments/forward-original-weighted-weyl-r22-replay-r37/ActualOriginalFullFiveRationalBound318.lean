module
public import ActualOriginalSmoothFullFiveKernel318
public section
noncomputable section
namespace ActualOriginalFullFiveRationalBound318
open QuadricCRTAssembly318 ActualOriginalScaledCircle318
open ActualOriginalCanonicalOverlapLength318 ActualOriginalSmoothFullFiveKernel318
open ActualOriginalFiveKernelSumBound318 ActualOriginalCompleteTwoAxisWeyl318
open ActualOriginalScaledDisplacementBlockCount318 ActualOriginalCompleteFrequencyBudget318
open ActualOriginalRationalBlockReciprocalSum318
open scoped ContDiff

/-- Complete FIVE-kernel rational bound for the actual original sum.
The denominator/error hypotheses are explicit and kappa must be nonzero;
no minor-domain denominator existence or final asymptotic is assumed. -/
theorem actual_smooth_full_five_rational_bound (κ : ℤ) (hκ : κ≠0) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ B : ℝ, 1≤B →
      ∀ a q : ℤ, 0<q → IsCoprime q a → ∀ t : ℝ,
      |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 →
      ‖scaledCircleSum κ t B W‖^2≤C*(2*R+4)^5*
        (((16*(⌈R*B⌉ : ℝ)/(q : ℝ)+2)*reciprocalBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)^4*
        ((16*((|κ|*⌈R*B⌉ : ℤ) : ℝ)/(q : ℝ)+2)*reciprocalBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)) := by
  obtain ⟨R,C,hR,hC,hb⟩ := actual_smooth_complete_five_kernel κ W hW hc
  refine ⟨R,C,hR,hC,fun B hB a q hq ha t ht => ?_⟩
  have hH := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have hHr : (0 : ℝ)≤(⌈R*B⌉ : ℝ) := by exact_mod_cast hH
  have hN : (0 : ℝ)≤2*(⌈R*B⌉ : ℝ)+1 := by positivity
  have hS := actual_complete_even_kernel_nonneg ⌈R*B⌉ (2*(⌈R*B⌉ : ℝ)+1) t hN
  have hT := actual_complete_even_kernel_nonneg (|κ|*⌈R*B⌉) (2*(⌈R*B⌉ : ℝ)+1) t hN
  have hs := actual_scaled_even_displacement_budget a q ⌈R*B⌉ t
    (2*(⌈R*B⌉ : ℝ)+1) hq ha hH ht hN
  have ht' := actual_scaled_even_displacement_budget a q (|κ|*⌈R*B⌉) t
    (2*(⌈R*B⌉ : ℝ)+1) hq ha (mul_nonneg (abs_nonneg κ) hH) ht hN
  apply (hb B hB t).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg (by linarith) _))
  apply (actual_five_kernel_nonzero_coefficient κ ⌈R*B⌉ _ t hκ hH hN).trans
  exact mul_le_mul (pow_le_pow_left₀ hS hs 4) ht' hT (pow_nonneg (hS.trans hs) 4)

end ActualOriginalFullFiveRationalBound318
