module
public import ActualTwoDescentInfinitePrimaryUnbounded318
public section
noncomputable section
namespace ActualTwoDescentInfinitePrimaryDivisible318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
open ActualTwoDescentCyclicLevelSquareRoot318 ActualTwoDescentInfinitePrimaryUnbounded318
variable (G : Type*) [CommGroup G] [Infinite G]

/-- An infinite abelian2-primary group with at most two involutions is genuinely2-divisible. -/
theorem actual_infinite_primary_square_surjective (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) :
    Function.Surjective (powMonoidHom (α:=G) 2) := by
  intro x
  obtain ⟨k,hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hP x
  obtain ⟨y,hy⟩ := actual_infinite_unbounded_levels G ht k
  obtain ⟨l,hl⟩ := isPGroup_iff_pow_pow_eq_one.mp hP y
  let N := max k l
  let X : powerLevel G N := ⟨x,actual_power_level_mono G (le_max_left k l) hk⟩
  let Y : powerLevel G N := ⟨y,actual_power_level_mono G (le_max_right k l) hl⟩
  letI := actual_power_levels_finite G ht N
  letI := actual_power_level_cyclic G ht hc N
  have hPN : IsPGroup 2 (powerLevel G N) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun z => ⟨N,Subtype.ext z.property⟩)
  obtain ⟨Z,hZ⟩ := actual_square_below_larger_order hPN k X Y (Subtype.ext hk)
    (fun h => hy (congrArg Subtype.val h))
  exact ⟨Z.val,congrArg Subtype.val hZ⟩

end ActualTwoDescentInfinitePrimaryDivisible318
