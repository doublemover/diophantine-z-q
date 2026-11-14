module
public import ActualTwoDescentActualShaPrimaryTwo318
public section
noncomputable section
namespace ActualTwoDescentActualShaHigherLevels318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentFinitePowerLevels318 ActualTwoDescentPowerLevelCyclic318
open ActualTwoDescentActualShaRankAlternative318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

lemma actual_sha_two_finite_bound (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    Finite (actualShaTwo n hn) ∧ Nat.card (actualShaTwo n hn) ≤ 2 := by
  rcases actual_sha_rank_alternative n hn hf hb hS with ⟨_,h,_⟩|⟨_,h,_⟩
  · exact ⟨Nat.finite_of_card_ne_zero (by rw [h]; decide),by omega⟩
  · exact ⟨Nat.finite_of_card_ne_zero (by rw [h]; decide),by omega⟩

/-- Every ACTUAL Sha[2^k] is finite cyclic of cardinality at most2^k; full Sha2∞ is NOT declared finite. -/
theorem actual_sha_higher_levels (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (k : ℕ) :
    Finite (powerLevel (actualShaPrimary n hn) k) ∧
    Nat.card (powerLevel (actualShaPrimary n hn) k) ≤ 2^k ∧
    IsCyclic (powerLevel (actualShaPrimary n hn) k) := by
  obtain ⟨ht,hc⟩ := actual_sha_two_finite_bound n hn hf hb hS
  letI := ht
  have ht' : Finite (powerLevel (actualShaPrimary n hn) 1) := Finite.of_equiv _ (primaryShaTwoEquiv n hn).toEquiv.symm
  have hc' : Nat.card (powerLevel (actualShaPrimary n hn) 1) ≤ 2 := by
    rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv]
    exact hc
  exact ⟨actual_power_levels_finite _ ht' k,actual_power_levels_card _ ht' hc' k,actual_power_level_cyclic _ ht' hc' k⟩

end ActualTwoDescentActualShaHigherLevels318
