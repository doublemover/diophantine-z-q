module
public import ActualTwoDescentTwoAdicUnits318
public section
noncomputable section
namespace ActualTwoDescentModEightObstruction318
open ActualTwoDescentTwoAdicUnits318
set_option maxHeartbeats 16000000

/-- The exact original cubic obstruction when both differences have
valuation1. For odd units U,W the residual square would equal nmod8,
which cannot be1 when n=3mod4. -/
theorem actual_mod8_obstruction (n : ℕ) (hn : n%4=3) (U W : ZMod 8)
    (hU : IsUnit U) (hW : IsUnit W)
    (he : W^2=((n : ZMod 8)+2*U)*U*(U+2*n)) : False := by
  have hw := actual_unit_square_mod8 W hW
  rw [hw] at he
  have hu : Nat.Coprime U.val 8 := (ZMod.isUnit_iff_coprime U.val 8).mp
    (by simpa only [ZMod.natCast_zmod_val] using hU)
  have hN : ((n : ZMod 8).val)%4=3 := by
    rw [ZMod.val_natCast,Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8),hn]
  generalize (n : ZMod 8)=N at he hN
  fin_cases N <;> fin_cases U <;> norm_num at hN hu he

/-- Transfer the finite obstruction through the ACTUAL reduction map
from the2-adic integers, preserving the full cubic equation. -/
theorem actual_two_unit_cubic_obstruction (n : ℕ) (hn : n%4=3) (U W : ℤ_[2])
    (hU : IsUnit U) (hW : IsUnit W)
    (he : W^2=((n : ℤ_[2])+2*U)*U*(U+2*n)) : False := by
  have hm := congrArg (PadicInt.toZModPow 3) he
  simp only [map_pow,map_mul,map_add,map_natCast,map_ofNat] at hm
  exact actual_mod8_obstruction n hn (PadicInt.toZModPow 3 U) (PadicInt.toZModPow 3 W)
    (hU.map (PadicInt.toZModPow 3)) (hW.map (PadicInt.toZModPow 3)) hm

end ActualTwoDescentModEightObstruction318
