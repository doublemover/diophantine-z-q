module
public import CompactMetricComparison318
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public section
noncomputable section
namespace ConformalCurvature318
open Filter Set CompactMetricComparison318
open scoped Topology
set_option maxHeartbeats 0

/-- Linearity of the actual second derivative for local C² functions. -/
theorem second_deriv_sub {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun t => f t - g t)) x =
      deriv (deriv f) x - deriv (deriv g) x := by
  have he : deriv (fun t => f t - g t) =ᶠ[𝓝 x] (fun t => deriv f t - deriv g t) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with t ht ht'
    exact deriv_fun_sub (ht.differentiableAt (by norm_num)) (ht'.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_fun_sub ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- The actual logarithmic ratio differentiation, with positivity only locally. -/
theorem second_deriv_log_ratio {f g : ℝ → ℝ} {x C : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hfpos : 0 < f x) (hgpos : 0 < g x) (hC : 0 < C) :
    deriv (deriv (fun t => Real.log (f t / (C * g t)))) x =
      deriv (deriv (fun t => Real.log (f t))) x -
      deriv (deriv (fun t => Real.log (g t))) x := by
  have hp : ∀ᶠ t in 𝓝 x, 0 < f t := hf.continuousAt.eventually (eventually_gt_nhds hfpos)
  have hq : ∀ᶠ t in 𝓝 x, 0 < g t := hg.continuousAt.eventually (eventually_gt_nhds hgpos)
  have he : (fun t => Real.log (f t / (C * g t))) =ᶠ[𝓝 x]
      (fun t => Real.log (f t) - Real.log (g t) - Real.log C) := by
    filter_upwards [hp, hq] with t ht ht'
    rw [Real.log_div ht.ne' (mul_pos hC ht').ne', Real.log_mul hC.ne' ht'.ne']
    ring
  rw [he.deriv.deriv_eq]
  simp only [deriv_sub_const_fun]
  exact second_deriv_sub (hf.log hfpos.ne') (hg.log hgpos.ne')

/-- Local C² along both coordinate axes, sufficient for the conformal Laplacian. -/
@[expose] def AxisC2 (f : ℝ × ℝ → ℝ) : Prop :=
  ContDiffAt ℝ 2 (fun t : ℝ => f (t, 0)) 0 ∧
  ContDiffAt ℝ 2 (fun t : ℝ => f (0, t)) 0

/-- Ordinary local conformal curvature, with the source's factor two. -/
@[expose] def curvature (rho : ℝ × ℝ → ℝ) : ℝ :=
  -laplacianAtOrigin (fun z => Real.log (rho z)) / (2 * rho (0, 0))

theorem laplacian_log_ratio (rho h : ℝ × ℝ → ℝ) (C : ℝ)
    (hrho : AxisC2 rho) (hh : AxisC2 h)
    (hrhopos : 0 < rho (0, 0)) (hhpos : 0 < h (0, 0)) (hC : 0 < C) :
    laplacianAtOrigin (fun z => Real.log (rho z / (C * h z))) =
      laplacianAtOrigin (fun z => Real.log (rho z)) -
      laplacianAtOrigin (fun z => Real.log (h z)) := by
  unfold laplacianAtOrigin
  rw [second_deriv_log_ratio hrho.1 hh.1 hrhopos hhpos hC,
    second_deriv_log_ratio hrho.2 hh.2 hrhopos hhpos hC]
  ring

/-- The actual curvature identity follows from differentiation; it is not
an assumed relation between opaque Laplacian and curvature symbols. -/
theorem conformal_curvature_identity (rho h : ℝ × ℝ → ℝ) (C : ℝ)
    (hrho : AxisC2 rho) (hh : AxisC2 h)
    (hrhopos : 0 < rho (0, 0)) (hhpos : 0 < h (0, 0)) (hC : 0 < C) :
    laplacianAtOrigin (fun z => Real.log (rho z / (C * h z))) =
      -2 * curvature rho * rho (0, 0) + 2 * curvature h * h (0, 0) := by
  rw [laplacian_log_ratio rho h C hrho hh hrhopos hhpos hC]
  unfold curvature
  field_simp
  ring

/-- Actual curvature-minus-one specializes the logarithmic ratio formula. -/
theorem hyperbolic_curvature_identity (rho h : ℝ × ℝ → ℝ) (C : ℝ)
    (hrho : AxisC2 rho) (hh : AxisC2 h)
    (hrhopos : 0 < rho (0, 0)) (hhpos : 0 < h (0, 0)) (hC : 0 < C)
    (hcurv : curvature h = -1) :
    laplacianAtOrigin (fun z => Real.log (rho z / (C * h z))) =
      -2 * curvature rho * rho (0, 0) - 2 * h (0, 0) := by
  rw [conformal_curvature_identity rho h C hrho hh hrhopos hhpos hC, hcurv]
  ring

end ConformalCurvature318
#print axioms ConformalCurvature318.second_deriv_sub
#print axioms ConformalCurvature318.second_deriv_log_ratio
#print axioms ConformalCurvature318.laplacian_log_ratio
#print axioms ConformalCurvature318.conformal_curvature_identity
#print axioms ConformalCurvature318.hyperbolic_curvature_identity
