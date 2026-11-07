module
public import CuspDerivative318
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public section
noncomputable section
namespace CuspCauchy318
open Metric
set_option maxHeartbeats 0

/-- Cauchy's estimate on translated circles inside the actual radius-1/100 disc. -/
theorem cauchy_derivative (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (q:ℂ) (hq:‖q‖≤(1:ℝ)/200) : ‖deriv G q‖≤25600 := by
  have hsub : closedBall q ((1:ℝ)/200) ⊆ closedBall 0 ((1:ℝ)/100) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hz
    have htri : ‖z‖≤‖z-q‖+‖q‖ := by simpa using norm_add_le (z-q) q
    linarith
  have hc : DiffContOnCl ℂ G (ball q ((1:ℝ)/200)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball q (by norm_num : (1:ℝ)/200≠0)]
    intro z hz
    have hzin := hsub hz
    rw [mem_closedBall,dist_zero_right] at hzin
    exact (hhol z hzin).differentiableWithinAt
  have hb : ∀z∈sphere q ((1:ℝ)/200),‖G z‖≤128 := by
    intro z hz
    apply hbound z
    have hz' := hsub (sphere_subset_closedBall hz)
    simpa only [mem_closedBall,dist_zero_right] using hz'
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/200) hc hb
  norm_num at he
  exact he

/-- The mean-value estimate is proved on the whole complex segment, not
inferred from a one-variable real derivative. -/
theorem constant_term_near (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (hzero:G 0=1) (q:ℂ) (hq:‖q‖≤(1:ℝ)/200) :
    ‖G q-1‖≤25600*‖q‖ := by
  have hd : ∀z∈closedBall (0:ℂ) ((1:ℝ)/200),DifferentiableAt ℂ G z := by
    intro z hz
    rw [mem_closedBall,dist_zero_right] at hz
    apply hhol z
    linarith
  have hb : ∀z∈closedBall (0:ℂ) ((1:ℝ)/200),‖deriv G z‖≤25600 := by
    intro z hz
    apply cauchy_derivative G hhol hbound z
    simpa only [mem_closedBall,dist_zero_right] using hz
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb
    (convex_closedBall (0:ℂ) ((1:ℝ)/200))
    (mem_closedBall_self (by norm_num : (0:ℝ)≤1/200))
    (show q∈closedBall (0:ℂ) ((1:ℝ)/200) by simpa using hq)
  simpa only [hzero,sub_zero] using hh

/-- Both small error bounds at the true cusp scale follow from holomorphy,
constant term one, and the single outer-disc majorant. -/
theorem cusp_errors (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (hzero:G 0=1) (q:ℂ) (hq:‖q‖≤Real.exp (-20*Real.pi)) :
    ‖G q-1‖<(1:ℝ)/4 ∧ ‖q*deriv G q‖<(1:ℝ)/4 := by
  have hsmall := hq.trans_lt CuspDerivative318.tiny_q
  have hq' : ‖q‖≤(1:ℝ)/200 := by linarith
  have hc := constant_term_near G hhol hbound hzero q hq'
  have hd := cauchy_derivative G hhol hbound q hq'
  constructor
  · linarith
  · rw [norm_mul]
    have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg q)
    linarith

/-- The derivative is the actual derivative of the Belyi coordinate built
from G, not a supplied complex number claimed to be that derivative. -/
theorem actual_belyi_derivative (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (hzero:G 0=1) (q:ℂ) (hq:‖q‖≤Real.exp (-20*Real.pi)) :
    (128:ℝ)≤‖deriv (fun z=>1728*z/G z) q‖ := by
  obtain ⟨he1,he2⟩ := cusp_errors G hhol hbound hzero q hq
  have hG : G q≠0 := by
    intro hz
    rw [hz,zero_sub,norm_neg,norm_one] at he1
    norm_num at he1
  have hd := (hasDerivAt_id q).const_mul (1728:ℂ)
  have hq' : ‖q‖≤(1:ℝ)/100 := by linarith [hq.trans_lt CuspDerivative318.tiny_q]
  have hder := hd.div (hhol q hq').hasDerivAt hG
  have hval : deriv (fun z=>1728*z/G z) q = 1728*(G q-q*deriv G q)/(G q)^2 := by
    change HasDerivAt (fun z=>1728*z/G z) ((1728*1*G q-1728*q*deriv G q)/(G q)^2) q at hder
    rw [hder.deriv]
    ring
  rw [hval]
  exact CuspDerivative318.derivative_formula_lower q (G q) (deriv G q) he1.le he2.le

end CuspCauchy318
#print axioms CuspCauchy318.cauchy_derivative
#print axioms CuspCauchy318.constant_term_near
#print axioms CuspCauchy318.cusp_errors
#print axioms CuspCauchy318.actual_belyi_derivative
