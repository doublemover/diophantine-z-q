module
public import ActualDyadicIntegerLift318
public section
noncomputable section
namespace ActualDyadicAmbientLift318
open QuadricCRTAssembly318 ActualOriginalModularLift318 ActualPrimitiveDigitLiftCount318
open ActualDyadicIntegerLift318 ActualAmbientQuadricLift318
set_option maxHeartbeats 26000000

@[expose] def Next (κ m : ℤ) (x : Coordinates ℤ) : Prop := (2*m)∣equation κ x

@[expose] def all_digit_equiv (κ m : ℤ) (hm : 2∣m) (x : Coordinates ℤ) (hx : Next κ m x) :
    DigitLifts κ 2 m x ≃ Coordinates (ZMod 2) where
  toFun h := h.1
  invFun h := ⟨h,(actual_dyadic_digit_test κ m hm x h).mpr hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_dyadic_digit_count (κ m : ℤ) (hm : 2∣m) (x : Coordinates ℤ) :
    Nat.card (DigitLifts κ 2 m x)=if Next κ m x then 32 else 0 := by
  classical
  by_cases hx : Next κ m x
  · rw [if_pos hx,Nat.card_congr (all_digit_equiv κ m hm x hx)]
    norm_num [Coordinates,Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card]
  · rw [if_neg hx]
    letI : IsEmpty (DigitLifts κ 2 m x) := ⟨fun h => hx ((actual_dyadic_digit_test κ m hm x h.1).mp h.2)⟩
    exact Nat.card_eq_zero_of_isEmpty

/-- ALL actual ambient original quadric lifts obey the same 32-or-0
rule. This is the producer whose successful base classes must be paired
by a separate dyadic involution before any p^4 average can be claimed. -/
theorem actual_dyadic_ambient_count (κ : ℤ) (m : ℕ) [NeZero m] (hm : 2∣m)
    (x : Quadric (κ:ZMod m)) :
    Nat.card (QuadricFiber κ m 2 x)=if Next κ (m:ℤ) (digits m x.1) then 32 else 0 := by
  rw [←Nat.card_congr (actual_quadric_fiber_equiv κ m 2 x)]
  exact actual_dyadic_digit_count κ (m:ℤ) (by exact_mod_cast hm) (digits m x.1)

end ActualDyadicAmbientLift318
