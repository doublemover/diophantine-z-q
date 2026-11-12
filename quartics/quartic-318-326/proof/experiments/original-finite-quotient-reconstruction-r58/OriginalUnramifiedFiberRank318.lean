module
public import OriginalQuotientRankFixed318
public import FiniteEtaleGeometricRank318
public section
noncomputable section
namespace OriginalUnramifiedFiberRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite p] [Flat p]
  (y : Spec (CommRingCat.of ℂ) ⟶ ProjectiveJLine318.scheme ℚ)

abbrev Fiber := pullback p y
abbrev fiberMap : Fiber p y ⟶ Spec (CommRingCat.of ℂ) := pullback.snd p y
abbrev FiberPoints := {s : Spec (CommRingCat.of ℂ) ⟶ Fiber p y // s ≫ fiberMap p y = 𝟙 _}
abbrev OriginalPoints := {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ p = y}

/-- Original over-base points and literal Cartesian fiber sections are
identified by the actual projections and lift, with both inverse laws. -/
@[expose] def pointsEquiv : FiberPoints p y ≃ OriginalPoints p y :=
  CartesianSectionPoints318.equiv (IsPullback.of_hasPullback p y)

/-- Cardinality of the actual geometric fiber, including its original
structure map, gives the rank of the SAME quotient at the SAME base point.
Etaleness is required only for this selected unramified fiber. -/
theorem rank [Etale (fiberMap p y)] (hcard : Nat.card (OriginalPoints p y) = 16) :
    p.finrank (y (IsLocalRing.closedPoint ℂ)) = 16 := by
  have h := FiniteEtaleGeometricRank318.card_sections_eq_rank ℂ (fiberMap p y)
  change Nat.card (FiberPoints p y) =
    (pullback.snd p y).finrank (IsLocalRing.closedPoint ℂ) at h
  rw [Scheme.Hom.finrank_pullback_snd] at h
  exact h.symm.trans ((Nat.card_congr (pointsEquiv p y)).trans hcard)
end OriginalUnramifiedFiberRank318
