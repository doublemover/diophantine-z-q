module
public import ActualTwoDescentFinitePrimaryCore318
public section
noncomputable section
namespace ActualTwoDescentInfinitePrimaryCore318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentPrimaryPowerLevels318
open ActualTwoDescentInfinitePrimaryDivisible318 ActualTwoDescentCompatiblePrimaryHalves318
variable (G : Type*) [CommGroup G] [Infinite G]

lemma actual_infinite_primary_core_top (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) : stableTwoCore G=⊤ := by
  apply top_unique
  intro x _ k
  let hs := actual_infinite_primary_square_surjective G hP ht hc
  exact ⟨halfTower hs x k,actual_half_tower_power hs x k⟩

end ActualTwoDescentInfinitePrimaryCore318
