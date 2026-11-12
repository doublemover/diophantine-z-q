module
public import ActualTwoDescentBetaGeneratesRationalImage318
public section
noncomputable section
namespace ActualTwoDescentBetaPointRankEquivalence318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentPointExtraction318 ActualTwoDescentRationalPointObstruction318
open ActualTwoDescentBetaGeneratesRationalImage318 ActualTwoDescentObstructionVanishing318
open ActualTwoDescentRationalQuotientAlternative318 ActualTwoDescentSameRationalBounds318
open ActualTwoDescentRationalEightClasses318 ActualTwoDescentActualQuotientBound318
open ActualTwoDescentBetaPointCardinalityBridge318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentAllPlacesIntersection318
open scoped BigOperators

/-- The original rational beta-point goal is EQUIVALENT to actual rational-group
infinitude once the constructed all-place cardinality is retained. Neither is asserted unconditionally. -/
theorem actual_beta_point_iff_infinite {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hn : (∏ i, p i) ≠ 0) (hb : monomial p beta ≠ 0)
    (hlocal : Nat.card (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=8) :
    Nonempty (KummerPoint (monomial p beta : ℚ) ((∏ i, p i : ℕ) : ℚ)) ↔
      Infinite (Point ((∏ i, p i : ℕ) : ℚ)) := by
  have HR : RationalEightBound (∏ i, p i) (monomial p beta) := by
    intro P
    exact actual_rational_eight_classes p hd hp2 hp3 a beta N C P
  obtain ⟨hf,hbound⟩ := actual_quotient_finite_bound _ _ hn hb HR
  constructor
  · rintro ⟨P⟩
    have hbeta := actual_global_image_of_kummer_point ((∏ i, p i : ℕ) : ℚ) (monomial p beta : ℚ)
      (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hb) P
    exact (actual_infinite_iff_local_global _ _ hf hbound hlocal).mpr
      (actual_beta_image_implies_local_global p hd hp2 hp3 a beta N C hn hb hbeta)
  · intro hInfinite
    have hcard := (actual_infinite_iff_quotient_eight _ _ hf hbound).mp hInfinite
    exact actual_beta_point_of_quotient_eight _ _ hn hb HR hcard

end ActualTwoDescentBetaPointRankEquivalence318
