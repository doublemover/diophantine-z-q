module
public import ActualTwoDescentStableCoreDivisibility318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace ActualTwoDescentReducedPrimaryQuotient318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentFinitePrimaryCore318 ActualTwoDescentInfinitePrimaryCore318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePrimaryImages318
variable (G : Type*) [CommGroup G]

abbrev reducedPrimary := G ⧸ stableTwoCore G

lemma actual_reduced_primary_finite (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) : Finite (reducedPrimary G) := by
  by_cases hf : Finite G
  · letI := hf; infer_instance
  · haveI : Infinite G := not_finite_iff_infinite.mp hf
    have hzero (x : reducedPrimary G) : x=1 := by
      obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective x
      apply (QuotientGroup.eq_one_iff y).mpr
      rw [actual_infinite_primary_core_top G hP ht hc]
      trivial
    haveI : Subsingleton (reducedPrimary G) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    infer_instance

lemma actual_reduced_primary_cyclic (hP : IsPGroup 2 G)
    (ht : Finite (powerLevel G 1)) (hc : Nat.card (powerLevel G 1) ≤ 2) : IsCyclic (reducedPrimary G) := by
  letI := actual_reduced_primary_finite G hP ht hc
  exact actual_finite_primary_image_cyclic hP ht hc (QuotientGroup.mk' (stableTwoCore G)) QuotientGroup.mk_surjective

end ActualTwoDescentReducedPrimaryQuotient318
