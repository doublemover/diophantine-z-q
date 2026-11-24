module
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic
public section
namespace OriginalKleinMarkedJet318
open Polynomial
variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
/-- Differentiation along the marked affine section, NEVER a derivation of
the number field K itself. No hom from the generic function field to K. -/
theorem along (D : Derivation ℤ A K) (x : A) (p : ℤ[X]) :
    D (eval₂ (Int.castRingHom A) x p) =
    eval₂ (Int.castRingHom K) (algebraMap A K x) (derivative p) * D x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval₂_add,map_add,hp,hq,add_mul]
  | monomial n c =>
    simp only [eval₂_monomial,derivative_monomial,Derivation.leibniz,Derivation.leibniz_pow,
      Int.coe_castRingHom,Derivation.map_intCast,Algebra.smul_def,
      map_intCast,map_pow,Int.cast_mul,Int.cast_natCast]
    rw [show algebraMap ℕ K n=(n:K) from rfl]
    ring

/-- The actual germ identity (not just its value!) transfers both T and dT.
The two candidate ordinary charts use the same identity with reciprocal
quartics on the x=∞ chart. -/
theorem read (D : Derivation ℤ A K) (x t : A) (n f : ℤ[X])
    (relation : t * eval₂ (Int.castRingHom A) x f = eval₂ (Int.castRingHom A) x n)
    (ok : eval₂ (Int.castRingHom K) (algebraMap A K x) f ≠ 0) :
    let e := fun p : ℤ[X] => eval₂ (Int.castRingHom K) (algebraMap A K x) p
    algebraMap A K t=e n/e f ∧
    D t=((e (derivative n)*e f-e n*e (derivative f))/(e f)^2)*D x := by
  dsimp only
  have ev (p : ℤ[X]) : algebraMap A K (eval₂ (Int.castRingHom A) x p) =
      eval₂ (Int.castRingHom K) (algebraMap A K x) p := by
    rw [hom_eval₂]
    rw [show (algebraMap A K).comp (Int.castRingHom A) = Int.castRingHom K from Subsingleton.elim _ _]
  have v := congrArg (algebraMap A K) relation
  rw [map_mul,ev,ev] at v
  have tval := (eq_div_iff ok).2 v
  refine ⟨tval,?_⟩
  have d := congrArg D relation
  rw [Derivation.leibniz,along,along,Algebra.smul_def,Algebra.smul_def,ev,tval] at d
  field_simp [ok] at d ⊢
  linear_combination d
end OriginalKleinMarkedJet318
#print axioms OriginalKleinMarkedJet318.along
#print axioms OriginalKleinMarkedJet318.read
