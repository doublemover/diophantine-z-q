module
public import SplitPointedCocycleNormalization318
public section
noncomputable section
namespace OriginalReducedFrameCocycle318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 OriginalThickenedFrameCocycle318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
lemma zero_preimage (V : X.Opens) :
    reduction R p ⁻¹ᵁ OriginalThickenedOpen318.fullOpen R p V = V := by
  rw [OriginalThickenedOpen318.fullOpen_eq, ← Scheme.Hom.comp_preimage, reduction_fst]
  all_goals rfl
lemma stable (V : X.Opens) : OriginalThickenedOpen318.fullOpen R p V ≤
    pullback.fst p (structureMap R) ⁻¹ᵁ
      (reduction R p ⁻¹ᵁ OriginalThickenedOpen318.fullOpen R p V) := by
  rw [zero_preimage, OriginalThickenedOpen318.fullOpen_eq]
variable {κ : Type u} (U : κ → X.Opens) (hU : ∀ k, IsAffine (U k).toScheme)
    (hc : (⊤ : X.Opens) ≤ ⨆ k, U k) (L : Deformation R p)
/-- Every actual pointed line on the original relative thickening yields a
unit cocycle on the complete thickened affine cover, reducing identically to1. -/
@[expose] def cocycle : UnitTransitionCocycle318.Cocycle
    (StructureUnitsSheaf318.units (thickening R p)).obj (opens R p U) :=
  SplitPointedCocycleNormalization318.normalized (reduction R p)
    (pullback.fst p (structureMap R)) L (opens R p U) (frames R p U hU L)
      (fun k => stable R p (U k))
lemma transition_reduces (k l : κ) :
    Units.map ((reduction R p).app (opens R p U k ⊓ opens R p U l)).hom.toMonoidHom
      ((cocycle R p U hU L).transition k l) = 1 :=
  SplitPointedCocycleNormalization318.transition_reduces (reduction R p)
    (pullback.fst p (structureMap R)) (reduction_fst R p) L (opens R p U)
      (frames R p U hU L) (fun k => stable R p (U k)) k l
/-- The normalized reduced-unit cocycle reconstructs the SAME original line.
This is the object-level bridge needed before taking additive logarithms. -/
@[expose] def reconstruction : L.line.object ≅
    CocycleModule318.object (opens R p U) (cocycle R p U hU L) :=
  SplitPointedCocycleNormalization318.reconstruction (reduction R p)
    (pullback.fst p (structureMap R)) L (opens R p U) (frames R p U hU L)
      (fun k => stable R p (U k)) (cover R p U hc)
end OriginalReducedFrameCocycle318
