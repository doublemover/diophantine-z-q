module
public import AdjoinRootSpecializedPoints318
public import Mathlib.FieldTheory.Separable
public section
noncomputable section
namespace AdjoinRootSeparablePointCount318
open Polynomial AdjoinRootSpecializedPoints318
variable {R : Type} [CommRing R] (Q : Polynomial R) (v : R →+* ℂ)

@[expose] def rootsEquivRootSet (hm : Q.Monic) :
    Roots Q v ≃ (Q.map v).rootSet ℂ where
  toFun z := ⟨z.1,Polynomial.mem_rootSet.mpr ⟨(hm.map v).ne_zero,by
    simpa only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using z.2⟩⟩
  invFun z := ⟨z.1,by
    have h := (Polynomial.mem_rootSet.mp z.2).2
    simpa only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using h⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

/-- Exact number of DISTINCT base-preserving complex points of the
whole monogenic order. Monicity retains degree under specialization. -/
theorem point_count (hm : Q.Monic) (hs : Q.Separable) :
    Nat.card (SchemePoints Q v) = Q.natDegree := by
  rw [Nat.card_congr ((schemeRootEquiv Q v).trans (rootsEquivRootSet Q v hm)),
    Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hs.map (IsAlgClosed.splits _)]
  exact hm.natDegree_map v

/-- Simplicity concerns the SAME specialized polynomial derivative,
not a generic-field derivative transported without specialization. -/
theorem every_point_simple (hs : Q.Separable) (e : Points Q v) :
    (Q.map v).derivative.eval (e.1 (AdjoinRoot.root Q)) ≠ 0 := by
  have hz := point_root Q v e
  exact (hs.map).eval₂_derivative_ne_zero (RingHom.id ℂ) hz
end AdjoinRootSeparablePointCount318
