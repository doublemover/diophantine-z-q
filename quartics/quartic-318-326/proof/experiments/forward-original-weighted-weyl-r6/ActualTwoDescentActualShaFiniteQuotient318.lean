module
public import ActualTwoDescentActualShaHigherLevels318
public section
noncomputable section
namespace ActualTwoDescentActualShaFiniteQuotient318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaHigherLevels318
open ActualTwoDescentFinitePrimaryImages318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentPrimaryPowerLevels318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- Any finite quotient of the ACTUAL full2-primary Sha is cyclic, including a future correctly identified finite Cassels-Tate quotient. -/
theorem actual_sha_finite_quotient_cyclic (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8)
    {H : Type*} [CommGroup H] [Finite H] (f : actualShaPrimary n hn →* H) (hs : Function.Surjective f) : IsCyclic H := by
  obtain ⟨ht,hc⟩ := actual_sha_two_finite_bound n hn hf hb hS
  letI := ht
  have ht' : Finite (powerLevel (actualShaPrimary n hn) 1) := Finite.of_equiv _ (primaryShaTwoEquiv n hn).toEquiv.symm
  have hc' : Nat.card (powerLevel (actualShaPrimary n hn) 1) ≤ 2 := by
    rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv]
    exact hc
  exact actual_finite_primary_image_cyclic (actual_sha_primary_is_two_group n hn) ht' hc' f hs

end ActualTwoDescentActualShaFiniteQuotient318
