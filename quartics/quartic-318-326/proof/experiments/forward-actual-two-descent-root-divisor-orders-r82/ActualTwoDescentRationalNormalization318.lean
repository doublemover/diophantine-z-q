module
public import ActualTwoDescentAdjoinThreeSupport318
public section
noncomputable section
namespace ActualTwoDescentRationalNormalization318
open ActualTwoDescentRationalPointPlaces318 ActualTwoDescentRationalSupport318
open ActualTwoDescentRationalSquarefree318 ActualTwoDescentAdjoinThreeSupport318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- ANY actual non-two-torsion rational point, not just a pre-normalized
class, supplies the exact original signed supported representatives and
nonzero rational square multipliers. -/
theorem actual_rational_normalization (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (P : RationalPoint (∏ i, p i)) :
    ∃ (ε δ : ZMod 2) (u v : Option U → ZMod 2),
      ∃ r s : ℚ, r ≠ 0 ∧ s ≠ 0 ∧
        P.x+3*(∏ i, p i : ℕ)=(firstRepresentative p δ u : ℚ)*r^2 ∧
        P.x-(∏ i, p i : ℕ)=(signedSecond p ε v : ℚ)*s^2 := by
  obtain ⟨δ,u,r,hr,hA⟩ := actual_rational_first_normalization p hd hp3 hn P
  obtain ⟨ε,v,s,hs,hB⟩ := actual_signed_supported_rational p hd _ P.minus_ne
    (actual_rational_second_support p hn P)
  refine ⟨ε,δ,u,v,r,s,hr,hs,hA,?_⟩
  simpa only [signedSecond,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast] using hB

end ActualTwoDescentRationalNormalization318
