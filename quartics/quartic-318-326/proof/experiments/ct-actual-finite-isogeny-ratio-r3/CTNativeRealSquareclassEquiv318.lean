module
public import ActualTwoDescentSquareClassQuotient318
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Real.Sqrt
import all ActualTwoDescentSquareClassQuotient318
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTNativeRealSquareclassEquiv318

open ActualTwoDescentSquareClassQuotient318
abbrev Bit := ZMod 2

def signOnUnits : ℝˣ →* Multiplicative Bit where
  toFun u := Multiplicative.ofAdd (if 0<(u:ℝ) then 0 else 1)
  map_one' := by
    change (if 0<(↑(1:ℝˣ):ℝ) then (0:Bit) else 1)=0
    rw [Units.val_one,if_pos zero_lt_one]
  map_mul' u w := by
    change (if 0<(↑(u*w):ℝ) then (0:Bit) else 1)=
      (if 0<(u:ℝ) then 0 else 1)+(if 0<(w:ℝ) then 0 else 1)
    rw [Units.val_mul]
    by_cases hu : 0<(u:ℝ) <;> by_cases hw : 0<(w:ℝ)
    · rw [if_pos hu,if_pos hw,if_pos (mul_pos hu hw),zero_add]
    · have hw' : (w:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hw) w.ne_zero
      rw [if_pos hu,if_neg hw,if_neg (not_lt_of_ge (mul_neg_of_pos_of_neg hu hw').le),zero_add]
    · have hu' : (u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
      rw [if_neg hu,if_pos hw,if_neg (not_lt_of_ge (mul_neg_of_neg_of_pos hu' hw).le),add_zero]
    · have hu' : (u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
      have hw' : (w:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hw) w.ne_zero
      rw [if_neg hu,if_neg hw,if_pos (mul_pos_of_neg_of_neg hu' hw')] <;> decide

/-- Actual sign factorization through real squareclasses. -/
def coordinates : SquareClass ℝ →* Multiplicative Bit :=
  QuotientGroup.lift (powMonoidHom (α:=ℝˣ) 2).range signOnUnits (by
    rintro _ ⟨u,rfl⟩
    change (if 0<(↑(u^2):ℝ) then (0:Bit) else 1)=0
    rw [Units.val_pow_eq_pow_val,if_pos (sq_pos_of_ne_zero u.ne_zero)])

theorem coordinates_on_value (x : ℝ) (hx : x≠0) :
    (coordinates (classOf x hx)).toAdd=if 0<x then 0 else 1 := rfl

private theorem coordinates_kernel (c : SquareClass ℝ) (h : coordinates c=1) : c=1 := by
  revert h
  refine QuotientGroup.induction_on c (fun u => ?_)
  have he : classOf (u:ℝ) u.ne_zero=QuotientGroup.mk u := by
    change QuotientGroup.mk (Units.mk0 (u:ℝ) u.ne_zero)=_
    have hU : Units.mk0 (u:ℝ) u.ne_zero=u := by apply Units.ext; rfl
    rw [hU]
  rw [←he]
  intro h
  have hbit := congrArg Multiplicative.toAdd h
  rw [coordinates_on_value] at hbit
  have hp : 0<(u:ℝ) := by
    by_contra hn
    rw [if_neg hn] at hbit
    exact (by decide : (1:Bit)≠0) hbit
  rw [←class_of_one]
  exact (class_of_eq_iff _ _ _ _).mpr
    ⟨Real.sqrt (u:ℝ),ne_of_gt (Real.sqrt_pos.2 hp),
      by rw [one_mul,Real.sq_sqrt hp.le]⟩

theorem coordinates_injective : Function.Injective coordinates := by
  intro x y h
  apply div_eq_one.mp
  apply coordinates_kernel
  rw [map_div,h,div_self']

theorem coordinates_surjective : Function.Surjective coordinates := by
  intro z
  have h : z.toAdd=0 ∨ z.toAdd=1 := (by decide : ∀ t : Bit, t=0 ∨ t=1) z.toAdd
  rcases h with h|h
  · exact ⟨1,Multiplicative.toAdd.injective ((congrArg Multiplicative.toAdd (map_one coordinates)).trans h.symm)⟩
  · refine ⟨classOf (-1:ℝ) (by norm_num),Multiplicative.toAdd.injective ?_⟩
    rw [coordinates_on_value,if_neg (by norm_num : ¬0<(-1:ℝ)),h]

def realScalarEquiv : SquareClass ℝ ≃* Multiplicative Bit :=
  MulEquiv.ofBijective coordinates ⟨coordinates_injective,coordinates_surjective⟩

end CTNativeRealSquareclassEquiv318

#print axioms CTNativeRealSquareclassEquiv318.realScalarEquiv
