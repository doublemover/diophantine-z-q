module
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic
public section
noncomputable section
namespace PolynomialAffineCoordinateEquiv318
open Polynomial
variable {R : Type*} [CommRing R] (t : R) (d : Rˣ)
@[expose] def forward : R[X] →ₐ[R] R[X] := aeval (C t+C (d : R)*X)
@[expose] def backward : R[X] →ₐ[R] R[X] := aeval (C (↑d⁻¹ : R)*(X-C t))

theorem forward_backward : (forward t d).comp (backward t d)=AlgHom.id R R[X] := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,forward,backward,aeval_X,map_mul,aeval_C,map_sub,AlgHom.id_apply]
  rw [add_sub_cancel_left,←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul]

theorem backward_forward : (backward t d).comp (forward t d)=AlgHom.id R R[X] := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,forward,backward,aeval_X,map_add,aeval_C,map_mul,AlgHom.id_apply]
  rw [←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]
  ring
@[expose] def equivalence : R[X] ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (forward t d) (backward t d) (forward_backward t d) (backward_forward t d)

theorem equivalence_X : equivalence t d X=C t+C (d : R)*X := aeval_X _
theorem equivalence_C (r : R) : equivalence t d (C r)=C r := aeval_C _ _
end PolynomialAffineCoordinateEquiv318
