module
public import ActualTwoDescentStablePrimaryCore318
public section
noncomputable section
namespace ActualTwoDescentFinitePrimaryCore318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318
variable (G : Type*) [CommGroup G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

lemma actual_finite_primary_core_bot (hP : IsPGroup 2 G) : stableTwoCore G=⊥ := by
  obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp hP
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y,hy⟩ := hx k
  change x=1
  rw [←hy,←hk]
  exact pow_card_eq_one'

end ActualTwoDescentFinitePrimaryCore318
