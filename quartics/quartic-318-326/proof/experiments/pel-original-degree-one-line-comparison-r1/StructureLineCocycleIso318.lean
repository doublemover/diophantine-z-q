module
public import StructureLineFrames318
public import UnitCocycleOne318
public import LineFrameReconstructionIso318
public import CocycleEqualityTransport318
public section
noncomputable section
namespace StructureLineCocycleIso318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (X:Scheme.{u}) {ι:Type u} (U:ι→X.Opens)
lemma cocycle_eq:
    LineFrameCocycle318.cocycle (SheafOfModules.unit X.ringCatSheaf) U
      (fun i=>StructureLineFrames318.frame X (U i))=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact StructureLineFrames318.transition_one X U i j
/-- The actual structure module, with identity original-section frames,
reconstructs the constant-one cocycle module on the supplied genuine cover. -/
@[expose] def iso (hc:(⊤:X.Opens)≤⨆i,U i):
    SheafOfModules.unit X.ringCatSheaf≅
      CocycleModule318.object U (UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U):=
  CocycleEqualityTransport318.changeTarget U
    (LineFrameReconstructionIso318.iso (SheafOfModules.unit X.ringCatSheaf) U
      (fun i=>StructureLineFrames318.frame X (U i)) hc) (cocycle_eq X U)
lemma hom_inv (hc:(⊤:X.Opens)≤⨆i,U i):
    (iso X U hc).hom≫(iso X U hc).inv=𝟙 _ :=(iso X U hc).hom_inv_id
lemma inv_hom (hc:(⊤:X.Opens)≤⨆i,U i):
    (iso X U hc).inv≫(iso X U hc).hom=𝟙 _ :=(iso X U hc).inv_hom_id
lemma hom_coefficient (hc:(⊤:X.Opens)≤⨆i,U i) (i:ι):
    (iso X U hc).hom≫CocycleModule318.coefficient U
      (UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U) i=
      LineFrameAdjunction318.coordinate (SheafOfModules.unit X.ringCatSheaf)
        (U i) (StructureLineFrames318.frame X (U i)):=by
  rw [iso,CocycleEqualityTransport318.changeTarget_coefficient]
  exact LineFrameReconstructionIso318.hom_coefficient _ _ _ hc i
end StructureLineCocycleIso318
