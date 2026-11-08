module
public import SourceTwistArithmetic318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace CubicWeierstrassPolynomial318
open Polynomial SourceTwistArithmetic318
set_option maxHeartbeats 700000
lemma twistProduct_ne_zero (i:Fin 4):twistProducts i≠0:=by
  unfold twistProducts
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>constants_ne_zero _)
@[expose] def twistUnit (i:Fin 4):ℚˣ:=Units.mk0 (twistProducts i) (twistProduct_ne_zero i)
@[expose] def radicand (i:Fin 4):ℚ[X]:=C (twistProducts i)*cubic i
@[expose] def shortPolynomial (i:Fin 4):ℚ[X]:=
  X^3+C (twistProducts i^2*cubicA i)*X+C (twistProducts i^3*cubicB i)
@[expose] def baseChange (i:Fin 4):ℚ[X]≃ₐ[ℚ]ℚ[X]:=by
  letI:=invertibleOfNonzero (Units.ne_zero (twistUnit i)⁻¹)
  exact Polynomial.algEquivCMulXAddC (↑(twistUnit i)⁻¹:ℚ) (centroid i)

lemma baseChange_apply (i:Fin 4) (p:ℚ[X]):
    baseChange i p=p.comp (C (↑(twistUnit i)⁻¹:ℚ)*X+C (centroid i)):=by
  simp [baseChange,Polynomial.algEquivCMulXAddC_apply,←Polynomial.comp_eq_aeval]

/-- Exact coefficient identity for the invertible affine base-coordinate
change from the cubic character equation to its short Weierstrass equation. -/
theorem changed_radicand (i:Fin 4):
    baseChange i (radicand i)=shortPolynomial i*(C (↑(twistUnit i)⁻¹:ℚ))^2:=by
  apply Polynomial.funext
  intro z
  have h:=congrArg (Polynomial.eval ((↑(twistUnit i)⁻¹:ℚ)*z)) (cubic_depression i)
  simp only [Polynomial.eval_comp,eval_add,eval_X,eval_C,eval_pow,eval_mul] at h
  rw [baseChange_apply]
  simp only [Polynomial.eval_comp,radicand,shortPolynomial,eval_mul,eval_add,eval_C,eval_X,eval_pow]
  rw [h]
  simp only [twistUnit,Units.val_inv_eq_inv_val,Units.val_mk0]
  have hq:=twistProduct_ne_zero i
  field_simp
end CubicWeierstrassPolynomial318
