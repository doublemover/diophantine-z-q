module
public import ActualTwoDescentActualShaZeroPrueferDuality318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrueferTwoCard318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaPrimaryTwo318
open ActualTwoDescentActualShaReducedPrimary318 ActualTwoDescentInfinitePrimarySharpLevels318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

lemma actual_infinite_sha_two_card (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) [Infinite (actualShaPrimary n hn)] :
    Nat.card (actualShaTwo n hn)=2 := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  have h := actual_infinite_primary_level_card _ (actual_sha_primary_is_two_group n hn) ht hc 1
  rw [Nat.card_congr (primaryShaTwoEquiv n hn).toEquiv] at h
  simpa only [pow_one] using h

end ActualTwoDescentActualShaPrueferTwoCard318
