module
public import ActualTwoDescentSignedRepresentativeTransport318
public section
noncomputable section
namespace ActualTwoDescentSignedLocalTranslation318
open ActualTwoDescentSignedRepresentativeTransport318 ActualTwoDescentTranslatedLocalPoint318
open ActualTwoDescentTranslatedSquarePair318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentSignedComparisons318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Literal signed representatives in the ACTUAL local curve image. -/
def SignedRepresentedAt (q : ℕ) [Fact q.Prime] (p : Option U → ℕ)
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  ∃ P : LocalPoint (p:=q) (∏ i, p i),
    SquarePair (P.x+3*(∏ i, p i : ℕ)) (P.x-(∏ i, p i : ℕ))
      (firstRepresentative p δ u : ℚ_[q]) (signedSecond p ε v : ℚ_[q])

/-- Actual torsion translation realizes the signed coefficient toggle at
EVERY prime. No local-signature equation or group quotient is assumed. -/
theorem actual_signed_local_translation (q : ℕ) [Fact q.Prime]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) (H : SignedRepresentedAt q p ε δ u v) :
    SignedRepresentedAt q p (ε+1) (δ+1) u (toggle 1 v) := by
  obtain ⟨P,HP⟩ := H
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Fact.out : (p i).Prime).ne_zero)
  let P' := translateLocal (q:=q) (∏ i, p i) hn0 P
  refine ⟨P',?_⟩
  have ht := actual_translated_square_pair (∏ i, p i : ℕ) P.x P.y
    (firstRepresentative p δ u : ℚ_[q]) (signedSecond p ε v : ℚ_[q])
    (Nat.cast_ne_zero.mpr hn0) P.x_ne P.minus_ne P.plus_ne P.curve HP
  exact actual_pair_rescale _ _ _ _ _ _ ((3 : ℚ_[q])^δ.val) (monomial p v : ℚ_[q])
    (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (monomial_pos p v).ne')
    (actual_first_torsion_transport p δ u) (actual_second_torsion_transport p ε v) ht

end ActualTwoDescentSignedLocalTranslation318
