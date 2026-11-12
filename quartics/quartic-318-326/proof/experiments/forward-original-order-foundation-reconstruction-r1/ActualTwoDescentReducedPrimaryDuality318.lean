module
public import ActualTwoDescentReducedPrimaryQuotient318
public section
noncomputable section
namespace ActualTwoDescentReducedPrimaryDuality318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentPrimaryPowerLevels318
open ActualTwoDescentReducedPrimaryQuotient318 ActualTwoDescentAlternatingCyclicPairing318
variable {G A : Type*} [CommGroup G] [CommGroup A]

/-- This is the exact finite quotient on which a Cassels-Tate-style global duality theorem would have to supply the pairing. -/
lemma actual_reduced_primary_zero_of_pairing (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2)
    (e : reducedPrimary G →* (reducedPrimary G →* A))
    (halt : ∀ x, e x x=1) (hnd : ∀ x, (∀ y, e x y=1) → x=1) :
    Subsingleton (reducedPrimary G) := by
  letI := actual_reduced_primary_cyclic G hP ht hc
  exact actual_nondegenerate_alternating_cyclic e halt hnd

lemma actual_core_top_of_reduced_zero (hz : Subsingleton (reducedPrimary G)) : stableTwoCore G=⊤ := by
  letI := hz
  apply top_unique
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

end ActualTwoDescentReducedPrimaryDuality318
