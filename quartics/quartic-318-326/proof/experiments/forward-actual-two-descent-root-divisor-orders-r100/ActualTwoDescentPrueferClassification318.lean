module
public import ActualTwoDescentDyadicPrueferInvolutions318
public section
noncomputable section
namespace ActualTwoDescentPrueferClassification318
set_option maxHeartbeats 16000000

open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentDyadicPrueferInvolutions318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentRankOnePrimaryEquivalence318
variable {G : Type} [CommGroup G] [Infinite G]

/-- Actual Prüfer classification in rank one: the infinite primary group is isomorphic to the standard dyadic subgroup of Q/Z. -/
theorem actual_infinite_primary_pruefer (hG : IsPGroup 2 G)
    (ftG : Finite (powerLevel G 1)) (hcG : Nat.card (powerLevel G 1) ≤ 2) : Nonempty (G ≃* PrueferTwo) := by
  letI := actual_pruefer_infinite
  exact actual_rank_one_primary_equivalence hG actual_pruefer_is_two_group ftG actual_pruefer_two_finite hcG actual_pruefer_two_card

end ActualTwoDescentPrueferClassification318
