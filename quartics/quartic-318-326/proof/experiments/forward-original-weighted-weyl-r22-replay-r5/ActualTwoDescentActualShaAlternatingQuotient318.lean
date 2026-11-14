module
public import ActualTwoDescentActualShaFiniteQuotient318
public section
noncomputable section
namespace ActualTwoDescentActualShaAlternatingQuotient318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaFiniteQuotient318
open ActualTwoDescentAlternatingCyclicPairing318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- The precise finite-quotient algebra needed by Cassels-Tate: any actual finite Sha2∞ quotient with a supplied genuine nondegenerate alternating pairing is zero. No pairing producer is assumed. -/
theorem actual_sha_alternating_finite_quotient_trivial (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8)
    {H A : Type*} [CommGroup H] [Finite H] [CommGroup A]
    (f : actualShaPrimary n hn →* H) (hs : Function.Surjective f)
    (e : H →* (H →* A)) (halt : ∀ x, e x x=1)
    (hnd : ∀ x, (∀ y, e x y=1) → x=1) : Subsingleton H := by
  letI := actual_sha_finite_quotient_cyclic n hn hf hb hS f hs
  exact actual_nondegenerate_alternating_cyclic e halt hnd

end ActualTwoDescentActualShaAlternatingQuotient318
