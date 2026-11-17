module
public import ActualDyadicRegularRecurrence318
public section
noncomputable section
namespace ActualOriginalDyadicBaseCount318
open QuadricCRTAssembly318 ActualOddRegularResidueTower318 ActualOddRegularLift318
open ActualOriginalModularLift318 ActualFullLocalDensityRecurrence318
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000

@[expose] def regularCoordinateEquiv (κ : ℤ) (m p : ℕ) :
    RegularResidues κ m p ≃
      {x : Coordinates (ZMod m) // equation (κ:ZMod m) x=0 ∧
        Regular (mapCoordinates (Int.castRingHom (ZMod p)) (digits m x))} where
  toFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Finite BASE certificate in ordinary kernel reduction. The exact
original coordinates, equation and mod2 regularity predicate are kept;
there is no native_decide or external count oracle. -/
lemma original_six_mod_eight_regular_count :
    ((Finset.univ : Finset (Coordinates (ZMod 8))).filter
      (fun x => equation (6:ZMod 8) x=0 ∧
        ((mapCoordinates (Int.castRingHom (ZMod 2)) (digits 8 x)).1,
          (mapCoordinates (Int.castRingHom (ZMod 2)) (digits 8 x)).2.1)≠((0,0),(0,0)))).card=4096 := by
  decide

lemma original_zero_mod_two_count :
    ((Finset.univ : Finset (Coordinates (ZMod 2))).filter
      (fun x => equation (0:ZMod 2) x=0)).card=16 := by decide
lemma original_two_mod_four_count :
    ((Finset.univ : Finset (Coordinates (ZMod 4))).filter
      (fun x => equation (2:ZMod 4) x=0)).card=256 := by decide

/-- The computed finite base is explicitly consumed by the actual
original regular residue type used by the whole dyadic recurrence. -/
theorem actual_original_regular_eight_count (κ : ℤ) (hκ : (κ:ZMod 8)=6) :
    Nat.card (RegularResidues κ 8 2)=4096 := by
  letI : DecidablePred (fun x : Coordinates (ZMod 8) => equation (κ:ZMod 8) x=0 ∧
      Regular (mapCoordinates (Int.castRingHom (ZMod 2)) (digits 8 x))) :=
    fun _ => by unfold Regular;infer_instance
  rw [Nat.card_congr (regularCoordinateEquiv κ 8 2),Nat.card_eq_fintype_card,Fintype.card_subtype,hκ]
  exact original_six_mod_eight_regular_count

lemma actual_original_dyadic_level_one (κ : ℤ) (hκ : (κ:ZMod 2)=0) : count κ 2 1=16 := by
  unfold count Quadric
  rw [pow_one,Nat.card_eq_fintype_card,Fintype.card_subtype,hκ]
  exact original_zero_mod_two_count
lemma actual_original_dyadic_level_two (κ : ℤ) (hκ : (κ:ZMod 4)=2) : count κ 2 2=256 := by
  unfold count Quadric
  norm_num only [show (2:ℕ)^2=4 by norm_num]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,hκ]
  exact original_two_mod_four_count

end ActualOriginalDyadicBaseCount318
