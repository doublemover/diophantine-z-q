module
public import PELPeriodRiemannForm318
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public section
noncomputable section
namespace PELOriginalHermitianForm318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318
variable (τ:ℂ) (hτ:0<τ.im)
local notation "E" => riemann τ hτ

lemma skew (z w:ComplexVectors):E z w= -E w z:=by
  have h:=alternating τ hτ (z+w)
  rw [add_left,add_right,add_right,alternating,alternating] at h
  linarith
lemma zero_left (w:ComplexVectors):E 0 w=0:=by
  simpa using smul_left τ hτ 0 0 w
lemma zero_right (z:ComplexVectors):E z 0=0:=by
  rw [skew,zero_left,neg_zero]
lemma I_move (z w:ComplexVectors):E (Complex.I • z) w= -E z (Complex.I • w):=by
  have h:=I_invariant τ hτ z (Complex.I • w)
  have hh:Complex.I • (Complex.I • w)=(-1:ℝ) • w:=by
    simp only [← mul_smul,Complex.I_mul_I,neg_one_smul]
  rw [hh,smul_right] at h
  linarith

/-- Positive Hermitian form on the SAME original complex period carrier.
The sign is fixed by E(z,iz)>0: Im H=-E, H is linear in its first slot. -/
@[expose] def form (z w:ComplexVectors):ℂ:=(E z (Complex.I • w):ℂ)-Complex.I*(E z w:ℂ)
lemma real_part (z w:ComplexVectors):(form τ hτ z w).re=E z (Complex.I • w):=by
  simp [form]
lemma imaginary_part (z w:ComplexVectors):(form τ hτ z w).im= -E z w:=by
  simp [form]
lemma form_add_left (z z' w:ComplexVectors):
    form τ hτ (z+z') w=form τ hτ z w+form τ hτ z' w:=by
  simp only [form,add_left,Complex.ofReal_add]
  ring
lemma form_add_right (z w w':ComplexVectors):
    form τ hτ z (w+w')=form τ hτ z w+form τ hτ z w':=by
  simp only [form,smul_add,add_right,Complex.ofReal_add]
  ring
lemma form_real_smul (a:ℝ) (z w:ComplexVectors):
    form τ hτ (a • z) w=(a:ℂ)*form τ hτ z w:=by
  simp only [form,smul_left,Complex.ofReal_mul]
  ring
lemma form_I (z w:ComplexVectors):
    form τ hτ (Complex.I • z) w=Complex.I*form τ hτ z w:=by
  apply Complex.ext
  · rw [real_part,I_invariant]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,imaginary_part,
      zero_mul,one_mul,zero_sub,neg_neg]
  · rw [imaginary_part,I_move]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,real_part,
      zero_mul,one_mul,zero_add,neg_neg]
lemma form_smul (a:ℂ) (z w:ComplexVectors):
    form τ hτ (a • z) w=a*form τ hτ z w:=by
  have ha:a • z=a.re • z+a.im • (Complex.I • z):=by
    ext i
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  rw [ha,form_add_left,form_real_smul,form_real_smul,form_I]
  calc
    _ = ((a.re:ℂ)+(a.im:ℂ)*Complex.I)*form τ hτ z w := by ring
    _ = _ := by rw [Complex.re_add_im]
lemma hermitian (z w:ComplexVectors):form τ hτ w z=star (form τ hτ z w):=by
  apply Complex.ext
  · simp only [real_part,Complex.star_def,Complex.conj_re]
    rw [skew,I_move] <;> ring
  · simp only [imaginary_part,Complex.star_def,Complex.conj_im]
    rw [skew τ hτ w z] <;> ring
lemma diagonal (z:ComplexVectors):form τ hτ z z=(E z (Complex.I • z):ℂ):=by
  simp [form,alternating]
lemma positive (z:ComplexVectors) (hz:z≠0):0<(form τ hτ z z).re:=by
  rw [real_part]
  exact PELPeriodRiemannForm318.positive τ hτ z hz

@[expose] def linear (w:ComplexVectors):ComplexVectors→ₗ[ℂ]ℂ where
  toFun z:=form τ hτ z w
  map_add':=fun z z'=>form_add_left τ hτ z z' w
  map_smul':=fun a z=>form_smul τ hτ a z w
@[expose] def continuousLinear (w:ComplexVectors):ComplexVectors→L[ℂ]ℂ:=
  (linear τ hτ w).toContinuousLinearMap

lemma skew_difference (z w:ComplexVectors):
    form τ hτ w z-form τ hτ z w=2*Complex.I*(E z w:ℂ):=by
  rw [hermitian]
  apply Complex.ext <;> simp [form,skew τ hτ w z] <;> ring
end PELOriginalHermitianForm318
