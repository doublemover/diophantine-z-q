module
public import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel
public section

namespace CTQuadraticCarrySwapAlgebra318

variable {A : Type*} [AddCommGroup A]

@[expose] def xor (a b : Bool) : Bool := if a then !b else b

@[expose] def mask (a : Bool) (t : A) : A := if a then t else 0

theorem map_mask (f : A →+ A) (a : Bool) (t : A) :
    f (mask a t) = mask a (f t) := by
  cases a <;> simp [mask]

private theorem mask_add (a : Bool) (t u : A) :
    mask a (t + u) = mask a t + mask a u := by
  cases a <;> simp [mask]

private theorem mask_mask (a b : Bool) (t : A) :
    mask a (mask b t) = mask (a && b) t := by
  cases a <;> cases b <;> rfl

theorem carry_law (a b : Bool) (t : A) :
    mask a t + mask b t - mask (xor a b) t = mask (a && b) (t + t) := by
  cases a <;> cases b <;> simp [mask,xor]

/-- Carry on Boolean addition is the positive carry, not its negative. -/
theorem carry_cycle (a b c : Bool) (t : A) :
    mask (b && c) t - mask (xor a b && c) t +
      mask (a && xor b c) t - mask (a && b) t = 0 := by
  cases a <;> cases b <;> cases c <;> simp [mask,xor] <;> abel

private theorem mixed_sign (a b c d : Bool) (s : A) (hs : s + s = 0) :
    mask (c && b) s - mask (d && a) s +
      mask (a && b) s + mask (c && d) s -
      mask (xor a c && xor b d) s = 0 := by
  have hn : -s = s := calc
    -s = -s + (s + s) := by rw [hs,add_zero]
    _ = s := by abel
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [mask,xor,sub_eq_add_neg,hn,hs,add_assoc] <;> abel

/-- Multiplicatively, Y^a X^(−b) s^(a b). -/
@[expose] def swapPrimitive (s X Y : A) (a b : Bool) : A :=
  mask a Y - mask b X + mask (a && b) s

/-- Explicit multiplicative ratio of the two cyclic positive carry
cochains, in the native additive notation for field units. -/
theorem differential (F : A →+ A) (s X Y : A) (a b c d : Bool)
    (hs : s + s = 0) (hS : F s = s)
    (hX : F X = X + mask a s) (hY : F Y = Y + mask b s) :
    F (swapPrimitive s X Y c d) - swapPrimitive s X Y (xor a c) (xor b d) +
      swapPrimitive s X Y a b =
      mask (a && c) (Y + Y) - mask (b && d) (X + X) := by
  have h : F (swapPrimitive s X Y c d) =
      mask c Y + mask (c && b) s - (mask d X + mask (d && a) s) +
        mask (c && d) s := by
    simp only [swapPrimitive,map_add,map_sub,map_mask,hY,hX,hS,mask_add,mask_mask]
  calc
    _ = (mask a Y + mask c Y - mask (xor a c) Y) -
        (mask b X + mask d X - mask (xor b d) X) +
        (mask (c && b) s - mask (d && a) s + mask (a && b) s +
          mask (c && d) s - mask (xor a c && xor b d) s) := by
      rw [h]
      unfold swapPrimitive
      abel
    _ = _ := by rw [carry_law,carry_law,mixed_sign a b c d s hs,add_zero]

end CTQuadraticCarrySwapAlgebra318
