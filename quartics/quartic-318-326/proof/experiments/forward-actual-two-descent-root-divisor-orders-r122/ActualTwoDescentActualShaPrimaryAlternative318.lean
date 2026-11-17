module
public import ActualTwoDescentCompatiblePrimaryHalves318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimaryAlternative318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentActualShaHigherLevels318 ActualTwoDescentPrimaryPowerLevels318
open ActualTwoDescentFinitePrimaryCyclic318 ActualTwoDescentInfinitePrimaryDivisible318
open ActualTwoDescentCompatiblePrimaryHalves318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- The actual full2-primary Sha is either finite cyclic, or infinite and genuinely2-divisible. No Cassels-Tate theorem is hidden in this alternative. -/
theorem actual_sha_primary_finite_or_divisible (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (Finite (actualShaPrimary n hn) ∧ IsCyclic (actualShaPrimary n hn)) ∨
    (Infinite (actualShaPrimary n hn) ∧ Function.Surjective (powMonoidHom (α:=actualShaPrimary n hn) 2)) := by
  obtain ⟨ht,hc⟩ := actual_sha_two_finite_bound n hn hf hb hS
  letI := ht
  have ht' : Finite (powerLevel (actualShaPrimary n hn) 1) := Finite.of_equiv _ (primaryShaTwoEquiv n hn).toEquiv.symm
  have hc' : Nat.card (powerLevel (actualShaPrimary n hn) 1) ≤ 2 := by
    rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv]
    exact hc
  by_cases hfin : Finite (actualShaPrimary n hn)
  · letI := hfin
    exact Or.inl ⟨hfin,actual_finite_primary_cyclic _ (actual_sha_primary_is_two_group n hn) hc'⟩
  · haveI : Infinite (actualShaPrimary n hn) := not_finite_iff_infinite.mp hfin
    exact Or.inr ⟨inferInstance,actual_infinite_primary_square_surjective _ (actual_sha_primary_is_two_group n hn) ht' hc'⟩

end ActualTwoDescentActualShaPrimaryAlternative318
