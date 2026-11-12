module
public import NormalizedLegendreProjectiveModel318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section
noncomputable section
namespace ThreeBranchLegendrePolynomial318
open Polynomial
variable (a b c:ℂ)
@[expose] def cubic:ℂ[X]:=(X-C a)*(X-C b)*(X-C c)
@[expose] def parameter:ℂ:=(c-a)/(b-a)
@[expose] def shortPolynomial:ℂ[X]:=
  X^3+C (NormalizedLegendreProjectiveModel318.A (parameter a b c))*X+
    C (NormalizedLegendreProjectiveModel318.B (parameter a b c))
variable (hab:b≠a)

/-- The actual coordinate substitution includes both the affine branch
normalization and the translation from Legendre t to short Weierstrass x. -/
@[expose] def baseChange:ℂ[X]≃ₐ[ℂ]ℂ[X]:=by
  letI:=invertibleOfNonzero (sub_ne_zero.mpr hab)
  exact Polynomial.algEquivCMulXAddC (b-a)
    (a+(b-a)*NormalizedLegendreProjectiveModel318.shift (parameter a b c))
lemma baseChange_apply (p:ℂ[X]):baseChange a b c hab p=
    p.comp (C (b-a)*X+C (a+(b-a)*
      NormalizedLegendreProjectiveModel318.shift (parameter a b c))):=by
  simp [baseChange,Polynomial.algEquivCMulXAddC_apply,←Polynomial.comp_eq_aeval]

lemma changed_cubic:baseChange a b c hab (cubic a b c)=
    shortPolynomial a b c*C ((b-a)^3):=by
  apply Polynomial.funext
  intro z
  rw [baseChange_apply]
  simp only [cubic,shortPolynomial,Polynomial.eval_comp,eval_mul,eval_sub,eval_add,
    eval_pow,eval_X,eval_C]
  dsimp [parameter,NormalizedLegendreProjectiveModel318.A,
    NormalizedLegendreProjectiveModel318.B,NormalizedLegendreProjectiveModel318.shift]
  field_simp [sub_ne_zero.mpr hab]
  <;> ring

@[expose] def rootScale:ℂ:=
  (IsAlgClosed.exists_pow_nat_eq ((b-a)^3) (by decide:0<2)).choose
lemma rootScale_square:rootScale a b^2=(b-a)^3:=
  (IsAlgClosed.exists_pow_nat_eq ((b-a)^3) (by decide:0<2)).choose_spec
include hab in
lemma rootScale_ne_zero:rootScale a b≠0:=by
  intro h
  have he:=rootScale_square a b
  rw [h,zero_pow (by decide:2≠0)] at he
  exact pow_ne_zero 3 (sub_ne_zero.mpr hab) he.symm
@[expose] def scaleUnit:ℂ[X]ˣ:=
  Units.map Polynomial.C.toMonoidHom (Units.mk0 (rootScale a b) (rootScale_ne_zero a b hab))
lemma scaled_cubic:baseChange a b c hab (cubic a b c)=
    shortPolynomial a b c*(scaleUnit a b hab:ℂ[X])^2:=by
  rw [changed_cubic]
  change _=shortPolynomial a b c*(C (rootScale a b))^2
  rw [←map_pow,rootScale_square]

include hab in
lemma parameter_nonexceptional (hca:c≠a) (hcb:c≠b):
    parameter a b c≠0∧parameter a b c≠1:=by
  refine ⟨div_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hab),?_⟩
  intro h
  have he:=div_mul_cancel₀ (c-a) (sub_ne_zero.mpr hab)
  change parameter a b c*(b-a)=c-a at he
  rw [h,one_mul] at he
  apply hcb
  linear_combination -he
end ThreeBranchLegendrePolynomial318
