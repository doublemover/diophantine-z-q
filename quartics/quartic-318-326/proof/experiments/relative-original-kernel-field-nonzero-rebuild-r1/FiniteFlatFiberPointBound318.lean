module
public import FiniteSchemePointBound318
public import Mathlib.AlgebraicGeometry.Fiber
public section
noncomputable section
namespace FiniteFlatFiberPointBound318
open AlgebraicGeometry CategoryTheory
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) [IsFinite p] [Flat p] (b : B)
instance finite_fiber : Finite (p ⁻¹' {b}) := by
  letI : IsFinite (p.fiberToSpecResidueField b) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  letI : Finite (p.fiber b) := FiniteSchemePointBound318.finite_points (B.residueField b) (p.fiberToSpecResidueField b)
  exact Finite.of_injective (p.fiberHomeo b).symm (p.fiberHomeo b).symm.injective
/-- Number of ALL original fiber points is bounded by the true module
rank, via the actual scheme-theoretic residue-field fiber. -/
lemma card_le_rank : Nat.card (p ⁻¹' {b})≤p.finrank b := by
  letI : IsFinite (p.fiberToSpecResidueField b) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  letI : Flat (p.fiberToSpecResidueField b) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  calc
    Nat.card (p ⁻¹' {b}) = Nat.card (p.fiber b) := Nat.card_congr (p.fiberHomeo b).symm.toEquiv
    _ ≤ (p.fiberToSpecResidueField b).finrank (IsLocalRing.closedPoint (B.residueField b)) :=
      FiniteSchemePointBound318.card_le_rank (B.residueField b) (p.fiberToSpecResidueField b)
    _ = p.finrank b := by
      rw [Scheme.Hom.fiberToSpecResidueField,Scheme.Hom.finrank_pullback_snd,Scheme.fromSpecResidueField_apply]
end FiniteFlatFiberPointBound318
