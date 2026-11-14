module
public import ActualTwoDescentRationalLocalImages318
public section
noncomputable section
namespace ActualTwoDescentRationalClassBound318
open ActualTwoDescentRationalPointPlaces318 ActualTwoDescentRationalNormalization318
open ActualTwoDescentRationalLocalImages318 ActualTwoDescentSignedAllBadNormalization318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSignedComparisons318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The finite arithmetic now constrains ANY actual rational point. Its
supported representative and local-image conditions are produced from
that point, not included as caller assumptions. -/
theorem actual_rational_class_bound (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (P : RationalPoint (∏ i, p i)) :
    ∃ ε c e : ZMod 2, ∃ r s : ℚ, r ≠ 0 ∧ s ≠ 0 ∧
      P.x+3*(∏ i, p i : ℕ)=(firstRepresentative p ε (c • ones (Option U)+e • beta) : ℚ)*r^2 ∧
      P.x-(∏ i, p i : ℕ)=(signedSecond p ε (ε • ones (Option U)) : ℚ)*s^2 := by
  obtain ⟨ε,δ,u,v,r,s,hr,hs,hA,hB⟩ := actual_rational_normalization p hd hp3 C.residue P
  have H := actual_rational_all_bad_images p P ε δ u v r s hr hs hA hB
  have Hp := (actual_signed_all_bad_normalization p ε δ u v).mp H
  obtain ⟨hδ,hv,c,e,hu⟩ := actual_represented_class_bound p hd hp2 hp3 a beta N C
    (δ+ε) u (toggle ε v) Hp.1
  have hdε : δ=ε := by linear_combination hδ
  have hvε : v=ε • ones (Option U) := by
    funext i
    have h := congrFun hv i
    change v i+ε*1=0 at h
    change v i=ε*1
    linear_combination h
  refine ⟨ε,c,e,r,s,hr,hs,?_,?_⟩
  · simpa only [hdε,hu] using hA
  · simpa only [hvε] using hB

end ActualTwoDescentRationalClassBound318
