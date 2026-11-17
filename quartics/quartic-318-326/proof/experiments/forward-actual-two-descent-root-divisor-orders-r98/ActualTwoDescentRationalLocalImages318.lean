module
public import ActualTwoDescentRationalNormalization318
public section
noncomputable section
namespace ActualTwoDescentRationalLocalImages318
open ActualTwoDescentRationalPointPlaces318 ActualTwoDescentSignedLocalTranslation318
open ActualTwoDescentSignedRealNormalization318 ActualTwoDescentSignedAllBadNormalization318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The SAME actual rational point and rational square multipliers give
all local images. Local points are not independently selected or assumed. -/
theorem actual_rational_all_bad_images (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (P : RationalPoint (∏ i, p i)) (ε δ : ZMod 2) (u v : Option U → ZMod 2)
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : P.x+3*(∏ i, p i : ℕ)=(firstRepresentative p δ u : ℚ)*r^2)
    (hB : P.x-(∏ i, p i : ℕ)=(signedSecond p ε v : ℚ)*s^2) :
    SignedAllBadRepresented p ε δ u v := by
  have hloc (q : ℕ) [Fact q.Prime] : SignedRepresentedAt q p ε δ u v := by
    refine ⟨toLocal q P,(r : ℚ_[q]),(s : ℚ_[q]),?_,?_,?_,?_⟩
    · exact_mod_cast hr
    · exact_mod_cast hs
    · change (P.x : ℚ_[q])+3*(∏ i, p i : ℕ)=(firstRepresentative p δ u : ℚ_[q])*(r : ℚ_[q])^2
      exact_mod_cast hA
    · change (P.x : ℚ_[q])-(∏ i, p i : ℕ)=(signedSecond p ε v : ℚ_[q])*(s : ℚ_[q])^2
      exact_mod_cast hB
  refine ⟨fun i => hloc (p i),hloc 3,hloc 2,?_⟩
  refine ⟨(P.x : ℝ),(P.y : ℝ),?_,?_,?_,?_,(r : ℝ),(s : ℝ),?_,?_,?_,?_⟩
  · exact_mod_cast P.x_ne
  · exact_mod_cast P.minus_ne
  · exact_mod_cast P.plus_ne
  · exact_mod_cast P.curve
  · exact_mod_cast hr
  · exact_mod_cast hs
  · exact_mod_cast hA
  · exact_mod_cast hB

end ActualTwoDescentRationalLocalImages318
