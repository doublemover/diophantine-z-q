module
public import ActualTwoDescentFinitePrimaryCyclic318
public section
noncomputable section
namespace ActualTwoDescentPowerLevelCyclic318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentFinitePrimaryCyclic318
variable (G : Type*) [CommGroup G]

def levelTwoInclusion (k : ℕ) : powerLevel (powerLevel G k) 1 →* powerLevel G 1 where
  toFun x := ⟨x.val.val,by
    have h := congrArg Subtype.val x.property
    simpa only [pow_one] using h⟩
  map_one' := rfl
  map_mul' x y := rfl

lemma actual_level_two_injective (k : ℕ) : Function.Injective (levelTwoInclusion G k) := by
  intro x y h
  apply Subtype.ext; apply Subtype.ext
  exact congrArg Subtype.val h

/-- Every actual higher torsion level is cyclic, with the original point/group inclusions retained. -/
lemma actual_power_level_cyclic (hf : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) (k : ℕ) :
    IsCyclic (powerLevel G k) := by
  letI := hf
  letI := actual_power_levels_finite G hf k
  have hp : IsPGroup 2 (powerLevel G k) := (isPGroup_iff_pow_pow_eq_one).mpr (fun x => ⟨k,Subtype.ext x.property⟩)
  apply actual_finite_primary_cyclic (powerLevel G k) hp
  exact (Nat.card_le_card_of_injective (levelTwoInclusion G k) (actual_level_two_injective G k)).trans hc

end ActualTwoDescentPowerLevelCyclic318
