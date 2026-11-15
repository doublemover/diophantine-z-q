module
public import ActualTwoDescentActualShaMaximalDivisible318
public section
noncomputable section
namespace ActualTwoDescentActualShaReducedDuality318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedPrimary318
open ActualTwoDescentReducedPrimaryDuality318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- Precise missing global duality producer: an actual pairing on the actual finite quotient. -/
def ActualReducedDuality (n : ℚ) (hn : n ≠ 0) : Prop :=
  ∃ e : actualShaReducedPrimary n hn →* (actualShaReducedPrimary n hn →* Multiplicative (AddCircle (1 : ℚ))),
    (∀ x, e x x=1) ∧ (∀ x, (∀ y, e x y=1) → x=1)

lemma actual_sha_reduced_zero_of_duality (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    Subsingleton (actualShaReducedPrimary n hn) := by
  obtain ⟨ht,hc⟩ := actual_sha_primary_level_bounds n hn hf hb hS
  obtain ⟨e,ha,hnon⟩ := hdual
  exact actual_reduced_primary_zero_of_pairing (actual_sha_primary_is_two_group n hn) ht hc e ha hnon

lemma actual_sha_core_full_of_duality (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    actualShaDivisibleCore n hn=⊤ :=
  actual_core_top_of_reduced_zero (actual_sha_reduced_zero_of_duality n hn hf hb hS hdual)

end ActualTwoDescentActualShaReducedDuality318
