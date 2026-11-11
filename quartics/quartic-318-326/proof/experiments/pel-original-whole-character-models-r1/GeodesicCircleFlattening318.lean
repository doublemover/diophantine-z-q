module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic
public section
noncomputable section
namespace GeodesicCircleFlattening318
open Complex Set
open scoped Topology
set_option maxHeartbeats 2400000

/-- Holomorphic straightening of the upper semicircle with real endpoints
a<b. The semicircle maps to the POSITIVE real axis. -/
@[expose] def flatten (a b : ℝ) (z : ℂ) : ℂ := -I*((z-a)/(b-z))
@[expose] def unflatten (a b : ℝ) (w : ℂ) : ℂ := (a+b*(I*w))/(1+I*w)

theorem endpoint_ne (b : ℝ) (z : ℂ) (hz : 0<z.im) : (b:ℂ)-z≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub] at hi
  linarith

theorem one_add_flatten_ne (a b : ℝ) (hab : a<b) (z : ℂ) (hz : (b:ℂ)-z≠0) :
    1+I*flatten a b z≠0 := by
  have hid : (1+I*flatten a b z)*((b:ℂ)-z)=b-a := by
    unfold flatten
    field_simp [hz]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  intro h
  rw [h,zero_mul] at hid
  have hr := congrArg Complex.re hid
  simp only [Complex.zero_re,Complex.sub_re,Complex.ofReal_re] at hr
  linarith

theorem unflatten_flatten (a b : ℝ) (hab : a<b) (z : ℂ) (hz : (b:ℂ)-z≠0) :
    unflatten a b (flatten a b z)=z := by
  have hn := one_add_flatten_ne a b hab z hz
  apply (div_eq_iff hn).mpr
  unfold flatten
  field_simp [hz]
  ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem endpoint_ne_unflatten (a b : ℝ) (hab : a<b) (w : ℂ) (hw : 1+I*w≠0) :
    (b:ℂ)-unflatten a b w≠0 := by
  have hid : ((b:ℂ)-unflatten a b w)*(1+I*w)=b-a := by
    unfold unflatten
    field_simp [hw]
    ring
  intro h
  rw [h,zero_mul] at hid
  have hr := congrArg Complex.re hid
  simp only [Complex.zero_re,Complex.sub_re,Complex.ofReal_re] at hr
  linarith

theorem flatten_unflatten (a b : ℝ) (hab : a<b) (w : ℂ) (hw : 1+I*w≠0) :
    flatten a b (unflatten a b w)=w := by
  have hn := endpoint_ne_unflatten a b hab w hw
  unfold flatten
  field_simp [hn]
  unfold unflatten
  field_simp [hw]
  ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem flatten_differentiableOn (a b : ℝ) :
    DifferentiableOn ℂ (flatten a b) {z : ℂ | (b:ℂ)-z≠0} := by
  intro z hz
  exact (differentiableAt_const.mul
    ((differentiableAt_id.sub_const _).div (differentiableAt_const.sub differentiableAt_id) hz)).differentiableWithinAt

theorem unflatten_differentiableOn (a b : ℝ) :
    DifferentiableOn ℂ (unflatten a b) {w : ℂ | 1+I*w≠0} := by
  intro w hw
  exact ((differentiableAt_const.add
    (differentiableAt_const.mul (differentiableAt_const.mul differentiableAt_id))).div
    (differentiableAt_const.add (differentiableAt_const.mul differentiableAt_id)) hw).differentiableWithinAt

/-- Exact original-coordinate circle equation in the imaginary part of
the holomorphic straightening map. -/
theorem flatten_im (a b : ℝ) (z : ℂ) :
    (flatten a b z).im=
      (Complex.normSq z-(a+b)*z.re+a*b)/Complex.normSq ((b:ℂ)-z) := by
  simp only [flatten,Complex.mul_im,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_mul,one_mul,zero_add,Complex.div_re,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,zero_sub,
    sub_zero,Complex.normSq_apply]
  ring

theorem flatten_re (a b : ℝ) (z : ℂ) :
    (flatten a b z).re=(b-a)*z.im/Complex.normSq ((b:ℂ)-z) := by
  simp only [flatten,Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_mul,one_mul,zero_sub,neg_neg,Complex.div_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,zero_sub,sub_zero]
  ring

theorem flatten_re_pos (a b : ℝ) (hab : a<b) (z : ℂ) (hz : 0<z.im) :
    0<(flatten a b z).re := by
  rw [flatten_re]
  exact div_pos (mul_pos (sub_pos.mpr hab) hz)
    (Complex.normSq_pos.mpr (endpoint_ne b z hz))

theorem flatten_real_iff_circle (a b : ℝ) (z : ℂ) (hz : 0<z.im) :
    (flatten a b z).im=0 ↔ Complex.normSq z-(a+b)*z.re+a*b=0 := by
  rw [flatten_im,div_eq_zero_iff]
  exact or_iff_left (Complex.normSq_pos.mpr (endpoint_ne b z hz)).ne'

/-- All straightened positive real points lie in the inverse analytic
chart, so the seam is not hidden in its pole. -/
theorem unflatten_real_denominator (x : ℝ) : 1+I*(x:ℂ)≠0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr
end GeodesicCircleFlattening318
