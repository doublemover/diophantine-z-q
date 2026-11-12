module
public import ActualTwoDescentInfinitePrimaryCore318
public section
noncomputable section
namespace ActualTwoDescentStableCoreMaximality318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentCompatiblePrimaryHalves318
variable (G : Type*) [CommGroup G]

/-- Every actual two-divisible subgroup lies in the same canonical stable core. -/
lemma actual_square_divisible_subgroup_le_core (H : Subgroup G)
    (hs : Function.Surjective (powMonoidHom (α:=H) 2)) : H ≤ stableTwoCore G := by
  intro x hx k
  let X : H := ⟨x,hx⟩
  exact ⟨(halfTower hs X k).val,congrArg Subtype.val (actual_half_tower_power hs X k)⟩

end ActualTwoDescentStableCoreMaximality318
