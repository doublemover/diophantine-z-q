module
public import ActualTwoDescentAllPlacesCubeImage318
public section
noncomputable section
namespace ActualTwoDescentAllPlacesExactCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualAllPlacesBound318 ActualTwoDescentActualCubeIndependence318
open ActualTwoDescentAllPlacesCubeImage318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentTorsionKummerValues318
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The ACTUAL all-place image has exactly eight elements, with every local
condition constructed/interpreted and no cohomological dimension premise. -/
theorem actual_all_places_card_eight (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (i0 i1 : Option U) (h0 : beta i0=0) (h1 : beta i1=1)
    (hn : (∏ i, p i) ≠ 0)
    (hbeta : retainedBetaClass (monomial p beta : ℚ) (Nat.cast_ne_zero.mpr (monomial_pos p beta).ne') ∈
      allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)) :
    Nat.card (allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn))=8 := by
  obtain ⟨hf,hupper⟩ := actual_all_places_finite_bound p hd hp2 hp3 a beta N C hn
  letI := hf
  have hlower := actual_all_places_card_ge_eight ((∏ i, p i : ℕ) : ℚ) (monomial p beta : ℚ)
    (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr (monomial_pos p beta).ne')
    (actual_cube_independent p hd beta i0 i1 h0 h1) hbeta
  exact Nat.le_antisymm hupper hlower

end ActualTwoDescentAllPlacesExactCardinality318
