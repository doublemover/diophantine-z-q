module
public import ContactOriginalTwistedBoundary318
public section
noncomputable section
namespace ContactOriginalPositiveTwistHOne318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
open LaurentVectorFiltration318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- A bound from the SAME original line's inverse Laurent columns implies
vanishing of the ACTUAL global derived H1 of its original tensor twist.
The input bound is on the old line, not on a new unknown transition. -/
lemma vanishing_of_bound (b : ℤ)
    (hb : ∀ i : Fin (ContactOriginalLaurentCoordinates318.finiteRank c L),
      (ContactOriginalLaurentCoordinates318.transition c L).symm (monomial i 0) ∈ upper b)
    (d : ℤ) (hd : b ≤ d)
    (x : OriginalLineMayerVietorisQuotient318.H1 (twist c L d)) : x = 0 := by
  obtain ⟨s,rfl⟩ := OriginalLineMayerVietorisQuotient318.boundary_surjective (twist c L d)
    (finiteOpen c) (infinityOpen c) (finite_affine c) (infinity_affine c) (cover c) x
  have hv : ContactOriginalTwistedRestriction318.coordinates c L d s ∈
      LaurentCechFinite318.boundary
        (LaurentPositiveTwistVanishing318.transition
          (ContactOriginalLaurentCoordinates318.transition c L) d) := by
    rw [LaurentPositiveTwistVanishing318.boundary_eq_top _ b hb d hd]
    trivial
  have hs := (ContactOriginalTwistedBoundary318.difference_iff c L d s).mpr hv
  rw [← OriginalLineMayerVietorisQuotient318.kernel_eq_range (twist c L d)
    (finiteOpen c) (infinityOpen c) (cover c)] at hs
  exact hs

/-- Genuine eventual vanishing for EVERY original line on the complete
Contact model. The positive twists are the ACTUAL line sheaves clutched
by T^n on the unchanged whole two-open cover; no coordinate compatibility,
chart freeness, acyclicity or transition bound is supplied by the caller.
This does not yet identify the twist with a projective O(n) pullback. -/
theorem exists_vanishing_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : OriginalLineMayerVietorisQuotient318.H1 (twist c L (n : ℤ)), x = 0 := by
  obtain ⟨b,hb⟩ := LaurentTransitionBounds318.exists_column_bound
    (ContactOriginalLaurentCoordinates318.transition c L).symm
  refine ⟨b.toNat,fun n hn x => vanishing_of_bound c L b hb n ?_ x⟩
  omega
end ContactOriginalPositiveTwistHOne318
