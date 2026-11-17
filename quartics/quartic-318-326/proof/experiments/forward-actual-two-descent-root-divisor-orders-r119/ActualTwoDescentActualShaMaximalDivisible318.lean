module
public import ActualTwoDescentActualShaReducedPrimary318
public section
noncomputable section
namespace ActualTwoDescentActualShaMaximalDivisible318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedPrimary318
open ActualTwoDescentStableCoreDivisibility318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- The subgroup used in the actual finite quotient is proved maximal divisible, not merely designated so. -/
theorem actual_sha_maximal_divisible (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) :
    (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : actualShaDivisibleCore n hn => x^m)) ∧
    ∀ H : Subgroup (actualShaPrimary n hn),
      (∀ m : ℕ, m ≠ 0 → Function.Surjective (fun x : H => x^m)) → H ≤ actualShaDivisibleCore n hn := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  exact actual_maximal_divisible_primary_core _ (actual_sha_primary_is_two_group n hn) ht hc

end ActualTwoDescentActualShaMaximalDivisible318
