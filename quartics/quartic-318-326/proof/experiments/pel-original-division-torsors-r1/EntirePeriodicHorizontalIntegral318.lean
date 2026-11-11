module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public section
noncomputable section
namespace EntirePeriodicHorizontalIntegral318
open Complex MeasureTheory intervalIntegral
variable (f:ℂ→ℂ) (hf:Differentiable ℂ f) (hp:Function.Periodic f 1)

/-- Moving the horizontal unit cycle vertically does not change the
integral of an actual entire periodic function. Derived from the actual
rectangle Cauchy theorem; no contour-shift hypothesis is supplied. -/
lemma imaginary_shift (y:ℝ):
    (∫x:ℝ in 0..1,f ((x:ℂ)+(y:ℂ)*Complex.I))=
      ∫x:ℝ in 0..1,f (x:ℂ):=by
  have h:=Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f 0 (1+(y:ℂ)*Complex.I) hf.differentiableOn
  have hv:(fun t:ℝ=>f (1+(t:ℂ)*Complex.I))=
      (fun t:ℝ=>f ((t:ℂ)*Complex.I)):=by
    funext t
    simpa only [add_comm] using hp ((t:ℂ)*Complex.I)
  norm_num only [Complex.zero_re,Complex.zero_im,Complex.add_re,Complex.add_im,
    Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_mul,sub_zero,zero_add,add_zero] at h
  rw [hv] at h
  linear_combination -h

/-- Translation by ANY complex number retains the same horizontal
integral. The real shift is genuine periodic integration, and the
imaginary shift is the preceding Cauchy rectangle calculation. -/
theorem complex_shift (w:ℂ):
    (∫x:ℝ in 0..1,f ((x:ℂ)+w))=∫x:ℝ in 0..1,f (x:ℂ):=by
  let g:ℝ→ℂ:=fun x=>f ((x:ℂ)+(w.im:ℂ)*Complex.I)
  have hg:Function.Periodic g 1:=by
    intro x
    simpa only [g,Complex.ofReal_add,Complex.ofReal_one,add_assoc,add_comm,add_left_comm] using
      hp ((x:ℂ)+(w.im:ℂ)*Complex.I)
  have he:∀x:ℝ,f ((x:ℂ)+w)=g (x+w.re):=by
    intro x
    simp only [g,Complex.ofReal_add,add_assoc,Complex.re_add_im]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right]
  have hi:=hg.intervalIntegral_add_eq w.re 0
  simp only [zero_add,add_comm 1 w.re] at hi ⊢
  rw [hi]
  exact imaginary_shift f hf hp w.im

/-- The exact Fourier coefficient shift, including the exponential
normalization required for the level-N recurrence. -/
@[expose] def coefficient (k:ℤ) (w:ℂ):ℂ:=
  ∫x:ℝ in 0..1,f ((x:ℂ)+w)*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(x:ℂ))
lemma weighted_periodic (k:ℤ):Function.Periodic
    (fun z:ℂ=>f z*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*z)) 1:=by
  intro z
  rw [hp]
  have he:Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(z+1))=
      Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*z):=by
    apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-k,?_⟩
    push_cast
    ring
  rw [he]
theorem coefficient_shift (k:ℤ) (w:ℂ):
    coefficient f k w=Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*w)*coefficient f k 0:=by
  let g:ℂ→ℂ:=fun z=>f z*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*z)
  have hg:Differentiable ℂ g:=hf.mul
    (Complex.differentiable_exp.comp (differentiable_const.mul differentiable_id))
  have ht:=complex_shift g hg (weighted_periodic f hp k) w
  have he:∀x:ℝ,f ((x:ℂ)+w)*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(x:ℂ))=
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*w)*g ((x:ℂ)+w):=by
    intro x
    change f ((x:ℂ)+w)*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(x:ℂ))=
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*w)*
        (f ((x:ℂ)+w)*Complex.exp (-2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*((x:ℂ)+w)))
    rw [mul_left_comm _ (f _)]
    congr 1
    rw [←Complex.exp_add]
    congr 1
    ring
  simp only [coefficient]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,ht]
  simp only [g,add_zero]
end EntirePeriodicHorizontalIntegral318
