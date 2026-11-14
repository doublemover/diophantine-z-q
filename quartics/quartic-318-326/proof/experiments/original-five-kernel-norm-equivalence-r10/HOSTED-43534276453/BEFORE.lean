module
public import TwoOpenUnitCocycleExt318
public section
noncomputable section
namespace OriginalTwoOpenReducedCocycle318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 AffineHOnePointedDeformation318
universe u
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Transport the entire dependent frame along equality of the original opens. -/
private def frameAlongOpenEq {Y : Scheme.{0}} (M : Y.Modules)
    (W Z : Y.Opens) (h : W = Z)
    (e : SheafOfModules.unit W.toScheme.ringCatSheaf ≅ M.restrict W.ι) :
    SheafOfModules.unit Z.toScheme.ringCatSheaf ≅ M.restrict Z.ι := by
  subst Z
  exact e

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ base R)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (L : Deformation R p)
include hU hV in
lemma affine (k : Bool) : IsAffine (TwoOpenAdditiveCocycle318.opens U V k).toScheme := by
  cases k
  · exact hU
  · exact hV
@[expose] def frames (k : Bool) : SheafOfModules.unit (thickOpens p U V k).toScheme.ringCatSheaf ≅
    L.line.object.restrict (thickOpens p U V k).ι := by
  have f := OriginalThickenedFrameCocycle318.frames R p (TwoOpenAdditiveCocycle318.opens U V)
    (affine U V hU hV) L k
  exact frameAlongOpenEq L.line.object _ _
    (OriginalThickenedOpen318.fullOpen_eq R p (TwoOpenAdditiveCocycle318.opens U V k)) f

lemma stable (k : Bool) : thickOpens p U V k ≤ pullback.fst p (structureMap R) ⁻¹ᵁ
    (reduction R p ⁻¹ᵁ thickOpens p U V k) := by
  exact le_of_eq (congrArg (fun W => (pullback.fst p (structureMap R)) ⁻¹ᵁ W)
    (OriginalThickenedOpenSections318.reduction_preimage R p
      (TwoOpenAdditiveCocycle318.opens U V k))).symm

@[expose] def cocycle : UnitTransitionCocycle318.Cocycle
    (StructureUnitsSheaf318.units (thickening R p)).obj (thickOpens p U V) :=
  SplitPointedCocycleNormalization318.normalized (reduction R p) (pullback.fst p (structureMap R))
    L (thickOpens p U V) (frames p U V hU hV L) (stable p U V)
@[expose] def overlapUnit : Γ(thickening R p,(pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V))ˣ :=
  (cocycle p U V hU hV L).transition false true
lemma overlapUnit_reduces : OriginalThickenedOpenSections318.reduce R p (U ⊓ V)
    (overlapUnit p U V hU hV L).val = 1 := by
  have h := congrArg Units.val
    (SplitPointedCocycleNormalization318.transition_reduces (reduction R p)
      (pullback.fst p (structureMap R)) (reduction_fst R p) L (thickOpens p U V)
      (frames p U V hU hV L) (stable p U V) false true)
  change (reduction R p).app ((pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V))
    (overlapUnit p U V hU hV L).val = 1 at h
  change X.presheaf.map (homOfLE _).op ((reduction R p).app
    ((pullback.fst p (structureMap R)) ⁻¹ᵁ (U ⊓ V)) (overlapUnit p U V hU hV L).val) = 1
  rw [h, map_one]
variable (hc : U ⊔ V = ⊤)
@[expose] def reconstruction : L.line.object ≅
    CocycleModule318.object (thickOpens p U V) (cocycle p U V hU hV L) :=
  SplitPointedCocycleNormalization318.reconstruction (reduction R p)
    (pullback.fst p (structureMap R)) L (thickOpens p U V) (frames p U V hU hV L)
      (stable p U V)
      (LinePullbackFrames318.preimage_cover (pullback.fst p (structureMap R))
        (TwoOpenAdditiveCocycle318.opens U V) (TwoOpenAdditiveCocycle318.cover U V hc))
end OriginalTwoOpenReducedCocycle318
