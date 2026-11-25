module
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section
noncomputable section

open Algebra Polynomial

namespace OriginalSameJPointedNormalConstants318

variable {k D L : Type*} [Field k] [CommRing D] [Field L]
  [Algebra k D] [Algebra k L] [Algebra D L] [IsScalarTower k D L]

abbrev order := (integralClosure D L).restrictScalars k

variable (e : (order (k:=k) (D:=D) (L:=L)) →ₐ[k] k)

/-- Every algebraic constant in the true function field already lies
in the same normal affine chart, because it is integral over its base. -/
def inChart (x : L) (hx : IsIntegral k x) : order (D:=D) (k:=k) (L:=L) :=
  ⟨x,hx.tower_top⟩

theorem full_eval_gives_minpoly_root (x : L) (hx : IsIntegral k x) :
    (minpoly k x).IsRoot (e (inChart (D:=D) x hx)) := by
  let A := order (k:=k) (D:=D) (L:=L)
  let b : A := inChart (D:=D) x hx
  have hzero : Polynomial.aeval b (minpoly k x) = 0 := by
    apply (show Function.Injective (A.val : A →ₐ[k] L) from Subtype.val_injective)
    calc
      A.val (Polynomial.aeval b (minpoly k x)) =
        Polynomial.aeval (A.val b) (minpoly k x) :=
          (Polynomial.aeval_algHom_apply A.val b (minpoly k x)).symm
      _ = 0 := minpoly.aeval k x
      _ = A.val 0 := (map_zero A.val).symm
  change (minpoly k x).eval (e b) = 0
  rw [← Polynomial.coe_aeval_eq_eval (e b)]
  calc
    _ = e (Polynomial.aeval b (minpoly k x)) :=
      Polynomial.aeval_algHom_apply e b (minpoly k x)
    _ = 0 := by rw [hzero,map_zero]

/-- No constant field enlargement. Consumes the actual complete
residue evaluation of this normal order, not just one χ-value. -/
theorem no_new_constants (x : L) (hx : IsIntegral k x) :
    algebraMap k L (e (inChart (D:=D) x hx)) = x :=
  minpoly.root hx (full_eval_gives_minpoly_root e x hx)

include e in
/-- The usual geometric irreducibility criterion now has its exact
field input for the same pointed normalization. -/
theorem relative_algebraic_closure : algebraicClosure k L = ⊥ := by
  apply bot_unique
  intro x hx
  have h : IsIntegral k x := mem_algebraicClosure_iff'.mp hx
  exact IntermediateField.mem_bot.mpr ⟨e (inChart (D:=D) x h), no_new_constants e x h⟩

end OriginalSameJPointedNormalConstants318

#print axioms OriginalSameJPointedNormalConstants318.full_eval_gives_minpoly_root
#print axioms OriginalSameJPointedNormalConstants318.no_new_constants
#print axioms OriginalSameJPointedNormalConstants318.relative_algebraic_closure
