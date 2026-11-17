module
public import ActualTwoDescentNestedPowerLevelInclusion318
public section
noncomputable section
namespace ActualTwoDescentInfinitePrimarySharpLevels318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
open ActualTwoDescentInfinitePrimaryUnbounded318 ActualTwoDescentNestedPowerLevelInclusion318
variable (G : Type*) [CommGroup G] [Infinite G]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- In the infinite branch every actual power level has EXACT cardinality2^k, not just an upper bound. -/
theorem actual_infinite_primary_level_card (hP : IsPGroup 2 G) (ht : Finite (powerLevel G 1))
    (hc : Nat.card (powerLevel G 1) ≤ 2) (k : ℕ) : Nat.card (powerLevel G k)=2^k := by
  obtain ⟨y,hy⟩ := actual_infinite_unbounded_levels G ht k
  obtain ⟨N,hN⟩ := isPGroup_iff_pow_pow_eq_one.mp hP y
  let Y : powerLevel G N := ⟨y,hN⟩
  letI := actual_power_levels_finite G ht N
  letI := actual_power_level_cyclic G ht hc N
  letI := actual_power_levels_finite G ht k
  have hpN : IsPGroup 2 (powerLevel G N) := isPGroup_iff_pow_pow_eq_one.mpr (fun z => ⟨N,Subtype.ext z.property⟩)
  obtain ⟨m,hm⟩ := IsPGroup.iff_card.mp hpN
  have hkm : k ≤ m := by
    by_contra h
    have hd : orderOf Y ∣ 2^k := (orderOf_dvd_natCard Y).trans (by rw [hm]; exact Nat.pow_dvd_pow 2 (by omega))
    exact hy (congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd))
  have hlevel : Nat.card (powerLevel (powerLevel G N) k)=2^k := by
    change Nat.card (powMonoidHom (α:=powerLevel G N) (2^k)).ker=2^k
    rw [IsCyclic.card_powMonoidHom_ker,hm,Nat.gcd_eq_right (Nat.pow_dvd_pow 2 hkm)]
  apply Nat.le_antisymm (actual_power_levels_card G ht hc k)
  rw [←hlevel]
  exact Nat.card_le_card_of_injective (nestedLevelInclusion G N k) (actual_nested_level_injective G N k)

end ActualTwoDescentInfinitePrimarySharpLevels318
