module
public import ActualTwoDescentCyclicLevelSquareRoot318
public section
noncomputable section
namespace ActualTwoDescentInfinitePrimaryUnbounded318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318
variable (G : Type*) [CommGroup G] [Infinite G]

/-- Finiteness of every actual power level forces an infinite primary group to contain elements beyond every bounded order. -/
lemma actual_infinite_unbounded_levels (ht : Finite (powerLevel G 1)) (k : ℕ) :
    ∃ y : G, y^(2^k) ≠ 1 := by
  by_contra! h
  letI := actual_power_levels_finite G ht k
  let f (y : G) : powerLevel G k := ⟨y,h y⟩
  have hi : Function.Injective f := fun x y hxy => congrArg Subtype.val hxy
  haveI : Finite G := Finite.of_injective f hi
  exact not_finite G

end ActualTwoDescentInfinitePrimaryUnbounded318
