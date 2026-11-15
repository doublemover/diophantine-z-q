module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic
public section
noncomputable section
namespace IntegralQuadraticPointZoom318
open Polynomial
set_option maxHeartbeats 1000000
variable {V : Type*} [CommRing V] (α β γ : Fin 4 → V) (t : V)
@[expose] def value (i : Fin 4) : V := α i*t^2+β i*t+γ i
@[expose] def product : V := ∏ i : Fin 4,value α β γ t i
@[expose] def cofactor (i : Fin 4) : V := ∏ j ∈ Finset.univ.erase i,value α β γ t j
@[expose] def scale : V := 4*product α β γ t
@[expose] def coordinate : V[X] := C t+C (scale α β γ t)*X
@[expose] def coefficient (i : Fin 4) : V[X] :=
  C (cofactor α β γ t i)*X*
    (C (2*α i*t+β i)+C (α i*scale α β γ t)*X)

theorem factor_product (i : Fin 4) : value α β γ t i*cofactor α β γ t i=product α β γ t := by
  classical
  exact Finset.mul_prod_erase _ _ (Finset.mem_univ i)

theorem coefficient_at_zero (i : Fin 4) : Polynomial.eval 0 (coefficient α β γ t i)=0 := by
  simp only [coefficient,eval_mul,eval_C,eval_add,eval_X,mul_zero,zero_mul]

/-- The exact point-centered transformation of ALL four original
quadratic radicands. The scale is an actual integral product; no root,
prime, contact difference or2 is inverted in the coefficient ring. -/
theorem transformed_radicand (i : Fin 4) :
    C (α i)*(coordinate α β γ t)^2+C (β i)*coordinate α β γ t+C (γ i) =
    C (value α β γ t i)*(1+4*coefficient α β γ t i) := by
  have hs : C (scale α β γ t) =
      4*C (value α β γ t i)*C (cofactor α β γ t i) := by
    rw [scale,←factor_product α β γ t i,map_mul,map_ofNat,map_mul]
    ring
  simp only [coordinate,coefficient,map_mul,hs]
  simp only [value,map_add,map_mul,map_pow]
  ring

/-- The new root variable has derivative1 at the actual point, even
in residue characteristic2. Over the characteristic-zero generic fiber
its original signed root is recovered by y_i*(1+2Z_i). -/
theorem root_identity {A : Type*} [CommRing A] (p q z : A)
    (hz : z^2+z=q) : (p*(1+2*z))^2=p^2*(1+4*q) := by
  rw [←hz]
  ring
end IntegralQuadraticPointZoom318
