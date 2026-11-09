module
public import PointedFrameTransitionReduction318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace OriginalThickenedFrameCocycle318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 OriginalThickenedOpen318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffine (U i).toScheme)
    (hc : (⊤ : X.Opens) ≤ ⨆ i, U i) (L : Deformation R p)
@[expose] def opens : ι → (thickening R p).Opens := fun i => fullOpen R p (U i)
include hc in
lemma cover : (⊤ : (thickening R p).Opens) ≤ ⨆ i, opens R p U i := by
  simp only [opens, fullOpen_eq]
  exact LinePullbackFrames318.preimage_cover (pullback.fst p (structureMap R)) U hc
/-- Genuine pointed-normalized frames of the unchanged original line on the
ENTIRE preimage of every member of the original affine cover. -/
@[expose] def frames (i : ι) :
    SheafOfModules.unit (opens R p U i).toScheme.ringCatSheaf ≅
      L.line.object.restrict (opens R p U i).ι := by
  letI := hU i
  exact OriginalThickenedPointedFrame318.restrictionFrame R p (U i) L
/-- All original double/triple transition laws come from actual original
frames, not a proposed Cech label. -/
@[expose] def cocycle : UnitTransitionCocycle318.Cocycle
    (StructureUnitsSheaf318.units (thickening R p)).obj (opens R p U) :=
  LineFrameCocycle318.cocycle L.line.object (opens R p U) (frames R p U hU L)
/-- The extracted original unit cocycle reconstructs the unchanged original
module sheaf; every pointed deformation is covered by this construction. -/
@[expose] def reconstruction : L.line.object ≅
    CocycleModule318.object (opens R p U) (cocycle R p U hU L) :=
  LineFrameReconstructionIso318.iso L.line.object (opens R p U) (frames R p U hU L) (cover R p U hc)
lemma reconstruction_coordinate (i : ι) :
    (reconstruction R p U hU hc L).hom ≫
      CocycleModule318.coefficient (opens R p U) (cocycle R p U hU L) i =
    LineFrameAdjunction318.coordinate L.line.object (opens R p U i) (frames R p U hU L i) :=
  LineFrameReconstructionIso318.hom_coefficient _ _ _ _ i
end OriginalThickenedFrameCocycle318
