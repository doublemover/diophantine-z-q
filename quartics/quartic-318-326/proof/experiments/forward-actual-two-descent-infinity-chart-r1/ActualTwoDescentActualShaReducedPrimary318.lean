module
public import ActualTwoDescentReducedPrimaryDuality318
public section
noncomputable section
namespace ActualTwoDescentActualShaReducedPrimary318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318 ActualTwoDescentActualShaHigherLevels318
open ActualTwoDescentStablePrimaryCore318 ActualTwoDescentStableCoreDivisibility318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentReducedPrimaryQuotient318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

abbrev actualShaDivisibleCore (n : ℚ) (hn : n ≠ 0) := stableTwoCore (actualShaPrimary n hn)
abbrev actualShaReducedPrimary (n : ℚ) (hn : n ≠ 0) := reducedPrimary (actualShaPrimary n hn)

lemma actual_sha_primary_level_bounds (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    Finite (powerLevel (actualShaPrimary n hn) 1) ∧ Nat.card (powerLevel (actualShaPrimary n hn) 1) ≤ 2 := by
  obtain ⟨ht,hc⟩ := actual_sha_two_finite_bound n hn hf hb hS
  letI := ht
  exact ⟨Finite.of_equiv _ (primaryShaTwoEquiv n hn).toEquiv.symm,by
    rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv]; exact hc⟩

/-- The quotient of the ACTUAL full primary Sha by its canonical maximal divisible subgroup is genuinely finite cyclic. -/
theorem actual_sha_reduced_finite_cyclic (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    Finite (actualShaReducedPrimary n hn) ∧ IsCyclic (actualShaReducedPrimary n hn) := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  exact ⟨actual_reduced_primary_finite _ (actual_sha_primary_is_two_group n hn) ht hc,
    actual_reduced_primary_cyclic _ (actual_sha_primary_is_two_group n hn) ht hc⟩

end ActualTwoDescentActualShaReducedPrimary318
