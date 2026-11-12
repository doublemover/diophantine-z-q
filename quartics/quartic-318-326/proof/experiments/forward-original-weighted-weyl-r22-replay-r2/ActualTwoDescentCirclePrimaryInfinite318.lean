module
public import ActualTwoDescentCirclePrimaryInvolutions318
public section
noncomputable section
namespace ActualTwoDescentCirclePrimaryInfinite318
set_option maxHeartbeats 16000000
open ActualTwoDescentCirclePrimaryInvolutions318
local instance (k : ℕ) : NeZero (2^(k+1)) := ⟨pow_ne_zero _ (by decide)⟩

def circleZModHom (k : ℕ) : Multiplicative (ZMod (2^(k+1))) →* Circle where
  toFun x := ZMod.toCircle x.toAdd
  map_one' := ZMod.toCircle.map_zero_eq_one
  map_mul' x y := ZMod.toCircle.map_add_eq_mul x.toAdd y.toAdd

lemma actual_circle_zmod_injective (k : ℕ) : Function.Injective (circleZModHom k) := by
  intro x y h
  exact congrArg Multiplicative.ofAdd (ZMod.injective_toCircle h)

def complexDyadicGenerator (k : ℕ) : CirclePrimary :=
  ⟨circleZModHom k (Multiplicative.ofAdd 1),k+1,by
    rw [←map_pow]
    have hz : (Multiplicative.ofAdd (1 : ZMod (2^(k+1))))^(2^(k+1))=1 := by
      change (2^(k+1)) • (1 : ZMod (2^(k+1)))=0
      simp [nsmul_eq_mul]
    rw [hz,map_one]⟩

lemma actual_complex_dyadic_order (k : ℕ) : orderOf (complexDyadicGenerator k)=2^(k+1) := by
  rw [←orderOf_injective CirclePrimary.subtype Subtype.val_injective (complexDyadicGenerator k)]
  change orderOf (circleZModHom k (Multiplicative.ofAdd 1))=2^(k+1)
  rw [orderOf_injective (circleZModHom k) (actual_circle_zmod_injective k)]
  exact ZMod.addOrderOf_one _

lemma actual_complex_dyadic_injective : Function.Injective complexDyadicGenerator := by
  intro i j h
  have ho := congrArg orderOf h
  rw [actual_complex_dyadic_order,actual_complex_dyadic_order] at ho
  have he := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) ho
  omega

lemma actual_circle_primary_infinite : Infinite CirclePrimary :=
  Infinite.of_injective complexDyadicGenerator actual_complex_dyadic_injective

end ActualTwoDescentCirclePrimaryInfinite318
