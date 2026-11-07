module
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Tactic
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace FixedPointTrace318
set_option maxHeartbeats 0

/-- Actual fixed-point equations, with no classification of modular stabilizers assumed. -/
theorem fixed_equations (g:GL (Fin 2) ℝ) (hg:g.val.det=1) (z:UpperHalfPlane)
    (hz:g•z=z) :
    2*g 1 0*z.re+g 1 1-g 0 0=0 ∧
    g 1 0*(z.re^2-z.im^2)+(g 1 1-g 0 0)*z.re-g 0 1=0 := by
  have hq := (gl_smul_eq_self_iff_quadratic (g:=g) (by rw [hg]; norm_num)).mp hz
  have hi := congrArg Complex.im hq
  have hr := congrArg Complex.re hq
  simp only [Complex.add_im,Complex.mul_im,Complex.sub_im,Complex.sub_re,Complex.neg_im,
    Complex.ofReal_im,Complex.ofReal_re,Complex.zero_im,coe_im,coe_re] at hi
  simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,
    Complex.ofReal_im,Complex.ofReal_re,Complex.zero_re,coe_im,coe_re] at hr
  have hh : (2*g 1 0*z.re+g 1 1-g 0 0)*z.im=0 := by linear_combination hi
  refine ⟨(mul_eq_zero.mp hh).resolve_right z.im_ne_zero,?_⟩
  linear_combination hr

/-- The exact trace identity at an actual fixed point. -/
theorem trace_identity (g:GL (Fin 2) ℝ) (hg:g.val.det=1) (z:UpperHalfPlane)
    (hz:g•z=z) :
    (g 0 0+g 1 1)^2+4*(g 1 0)^2*z.im^2=4 := by
  obtain ⟨hi,hr⟩:=fixed_equations g hg z hz
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa [Matrix.det_fin_two] using hg
  linear_combination 4*hd+(2*g 1 0*z.re+g 1 1-g 0 0)*hi-4*g 1 0*hr

/-- Every determinant-one real matrix fixing an upper-half-plane point has trace in [-2,2]. -/
theorem trace_bounds (g:GL (Fin 2) ℝ) (hg:g.val.det=1) (z:UpperHalfPlane)
    (hz:g•z=z) : -2≤g 0 0+g 1 1 ∧ g 0 0+g 1 1≤2 := by
  have he:=trace_identity g hg z hz
  have hn:=mul_nonneg (sq_nonneg (g 1 0)) (sq_nonneg z.im)
  constructor <;> nlinarith

/-- Equality at the trace-two endpoint forces the actual matrix to be identity. -/
theorem eq_one_of_trace_two (g:GL (Fin 2) ℝ) (hg:g.val.det=1) (z:UpperHalfPlane)
    (hz:g•z=z) (ht:g 0 0+g 1 1=2) : g=1 := by
  have he:=trace_identity g hg z hz
  rw [ht] at he
  have hc:g 1 0=0 := by
    have hh : (g 1 0)^2*z.im^2=0 := by nlinarith
    have hc2 : (g 1 0)^2=0 := (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 2 z.im_ne_zero)
    nlinarith [hc2]
  obtain ⟨hi,hr⟩:=fixed_equations g hg z hz
  have ha:g 0 0=1 := by rw [hc] at hi; linarith
  have hd:g 1 1=1 := by linarith
  have hb:g 0 1=0 := by rw [hc,ha,hd] at hr; linarith
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha,hb,hc,hd]
end FixedPointTrace318
