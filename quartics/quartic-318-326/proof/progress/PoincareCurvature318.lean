module
public import FiniteLaplacian318
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public section
noncomputable section
open Filter Set CompactMetricComparison318 ConformalCurvature318 FiniteLaplacian318
open scoped Topology
namespace PoincareCurvature318
set_option maxHeartbeats 0

/-- The actual ordinary hyperbolic coefficient at an upper-half-plane point. -/
@[expose] def coefficient (z:UpperHalfPlane) : ℝ := 1/z.im^2
@[expose] def localCoefficient (z:UpperHalfPlane) (w:ℝ×ℝ) : ℝ := 1/(z.im+w.2)^2

theorem coefficient_positive (z:UpperHalfPlane) : 0<coefficient z := by
  exact one_div_pos.mpr (sq_pos_of_pos z.im_pos)

theorem local_axisC2 (z:UpperHalfPlane) : AxisC2 (localCoefficient z) := by
  constructor
  · change ContDiffAt ℝ 2 (fun _t:ℝ=>1/(z.im+0)^2) 0
    exact contDiffAt_const
  · apply ContDiffAt.div contDiffAt_const
    · exact (contDiffAt_const.add contDiffAt_id).pow 2
    · simpa using pow_ne_zero 2 z.im_ne_zero

theorem log_vertical (y t:ℝ) : Real.log (1/(y+t)^2)=(-2)*Real.log (y+t) := by
  rw [one_div,Real.log_inv,Real.log_pow]
  ring

theorem log_linear_second (y:ℝ) (hy:y≠0) :
    deriv (deriv (fun t:ℝ=>Real.log (y+t))) 0=-(1:ℝ)/y^2 := by
  have hf:ContDiffAt ℝ 2 (fun t:ℝ=>y+t) 0:=contDiffAt_const.add contDiffAt_id
  rw [second_deriv_log hf (by simpa using hy)]
  have hd:deriv (fun t:ℝ=>y+t)=(fun _=>1) := by
    funext t
    exact ((hasDerivAt_id t).const_add y).deriv
  rw [hd]
  simp only [deriv_const,add_zero]
  ring

theorem laplacian_log (z:UpperHalfPlane) :
    laplacianAtOrigin (fun w=>Real.log (localCoefficient z w))=2/z.im^2 := by
  unfold laplacianAtOrigin
  have hx:(fun t:ℝ=>Real.log (localCoefficient z (t,0)))=(fun _=>Real.log (1/z.im^2)) := by
    funext t; simp [localCoefficient]
  have hy:(fun t:ℝ=>Real.log (localCoefficient z (0,t)))=(fun t=>(-2)*Real.log (z.im+t)) := by
    funext t; exact log_vertical z.im t
  rw [hx,hy]
  have hc:deriv (deriv (fun _t:ℝ=>Real.log (1/z.im^2))) 0=0 := by
    rw [deriv_const']
    exact deriv_const _ _
  rw [hc,zero_add]
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  rw [log_linear_second z.im z.im_ne_zero]
  ring

/-- The computed ordinary conformal curvature is exactly minus one. -/
theorem curvature_eq_neg_one (z:UpperHalfPlane) : curvature (localCoefficient z)=-1 := by
  rw [curvature,laplacian_log,localCoefficient]
  simp only [add_zero]
  field_simp

theorem translated_coefficient (z:UpperHalfPlane) (w:ℝ×ℝ)
    (hw:0<z.im+w.2) :
    localCoefficient z w=coefficient ⟨(z:ℂ)+((w.1:ℂ)+w.2*Complex.I),by simpa using hw⟩ := by
  change 1/(z.im+w.2)^2=1/(((z:ℂ)+((w.1:ℂ)+w.2*Complex.I)).im)^2
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,UpperHalfPlane.coe_im,mul_one,mul_zero,add_zero,zero_add]

/-- Exact cotangent coordinate normalization in the uniformizing coordinate. -/
theorem cotangent_normalization (z:UpperHalfPlane) :
    2/Real.sqrt (coefficient z)=2*z.im := by
  rw [coefficient,Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_sq_eq_abs,
    abs_of_pos z.im_pos]
  field_simp

end PoincareCurvature318
#print axioms PoincareCurvature318.curvature_eq_neg_one
