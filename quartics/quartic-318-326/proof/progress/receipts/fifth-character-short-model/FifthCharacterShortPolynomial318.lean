module
public import FifthCharacterPolynomial318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace FifthCharacterShortPolynomial318
open Polynomial
set_option maxHeartbeats 650000
@[expose] def A:ℚ:= -30483
@[expose] def B:ℚ:=1993518
@[expose] def xScale:ℚˣ:=Units.mk0 (-230496/25) (by norm_num)
@[expose] def yScale:ℚˣ:=Units.mk0 (-14/125) (by norm_num)
@[expose] def shift:ℚ:=2178/25
@[expose] def shortPolynomial:ℚ[X]:=X^3+C A*X+C B
@[expose] def baseChange:ℚ[X]≃ₐ[ℚ]ℚ[X]:=by
  letI:=invertibleOfNonzero (Units.ne_zero xScale⁻¹)
  exact Polynomial.algEquivCMulXAddC (↑xScale⁻¹:ℚ) (-shift*(↑xScale⁻¹:ℚ))
lemma baseChange_apply (p:ℚ[X]) :
    baseChange p=p.comp (C (↑xScale⁻¹:ℚ)*X+C (-shift*(↑xScale⁻¹:ℚ))):=by
  simp [baseChange,Polynomial.algEquivCMulXAddC_apply,←Polynomial.comp_eq_aeval]
/-- Exact reciprocal cubic normalization, retaining both rational scales. -/
theorem changed_reciprocal : baseChange FifthCharacterPolynomial318.reciprocal=
    shortPolynomial*(C (↑yScale⁻¹:ℚ))^2:=by
  apply Polynomial.funext
  intro z
  rw [baseChange_apply]
  norm_num [FifthCharacterPolynomial318.reciprocal,shortPolynomial,A,B,xScale,yScale,shift,
    Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Units.val_inv_eq_inv_val]
  ring
/-- The exact resulting short model is nonsingular over Q. -/
theorem discriminant_exact : -16*(4*A^3+27*B^2)=95996101017600:=by norm_num [A,B]
theorem discriminant_unit : IsUnit (-16*(4*A^3+27*B^2)):=by
  rw [discriminant_exact]
  exact isUnit_iff_ne_zero.mpr (by norm_num)
end FifthCharacterShortPolynomial318
