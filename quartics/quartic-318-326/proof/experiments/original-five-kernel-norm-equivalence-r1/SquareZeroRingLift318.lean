module
public import SquareZeroUnit318
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace SquareZeroRingLift318
open SquareZeroUnit318
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (e : B) (he : e * e = 0)
/-- Literal coefficient-plus-epsilon evaluation in the original target ring. -/
@[expose] def lift : Dual A →+* B where
  toFun x := f x.fst + e * f x.snd
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring
  map_mul' x y := by
    change f (x.fst * y.fst) + e * f (x.fst * y.snd + x.snd * y.fst) =
      (f x.fst + e * f x.snd) * (f y.fst + e * f y.snd)
    simp only [map_mul, map_add]
    calc
      _ = (f x.fst + e * f x.snd) * (f y.fst + e * f y.snd) -
          (e * e) * (f x.snd * f y.snd) := by ring
      _ = _ := by rw [he]; ring
@[simp] lemma lift_inl (a : A) : lift f e he (TrivSqZeroExt.inl a) = f a := by simp [lift]
@[simp] lemma lift_inr (a : A) : lift f e he (TrivSqZeroExt.inr a) = e * f a := by simp [lift]
@[simp] lemma lift_apply (x : Dual A) : lift f e he x = f x.fst + e * f x.snd := rfl
@[expose] def congr (g : A ≃+* B) : Dual A ≃+* Dual B where
  __ := SquareZeroUnit318.map A g.toRingHom
  invFun := SquareZeroUnit318.map B g.symm.toRingHom
  left_inv x := by apply TrivSqZeroExt.ext <;> simp
  right_inv x := by apply TrivSqZeroExt.ext <;> simp
end SquareZeroRingLift318
