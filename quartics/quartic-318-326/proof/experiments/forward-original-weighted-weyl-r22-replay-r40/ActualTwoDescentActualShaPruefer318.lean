module
public import ActualTwoDescentPrueferClassification318
public section
noncomputable section
namespace ActualTwoDescentActualShaPruefer318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentActualShaHigherLevels318 ActualTwoDescentPrimaryPowerLevels318
open ActualTwoDescentPrueferClassification318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- The ACTUAL infinite2-primary Sha is now identified with a genuine dyadic Prüfer group, not just called corank one. -/
theorem actual_infinite_sha_pruefer (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) [Infinite (actualShaPrimary n hn)] :
    Nonempty (actualShaPrimary n hn ≃* PrueferTwo) := by
  obtain ⟨ht,hc⟩ := actual_sha_two_finite_bound n hn hf hb hS
  letI := ht
  have ht' : Finite (powerLevel (actualShaPrimary n hn) 1) := Finite.of_equiv _ (primaryShaTwoEquiv n hn).toEquiv.symm
  have hc' : Nat.card (powerLevel (actualShaPrimary n hn) 1) ≤ 2 := by
    rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv]
    exact hc
  exact actual_infinite_primary_pruefer (actual_sha_primary_is_two_group n hn) ht' hc'

end ActualTwoDescentActualShaPruefer318
