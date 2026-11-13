module
public import UnitCocycleInverse318
public import TensorLineCocycle318
public import CocycleCanonicalTransitions318
public import StructureLineCocycleIso318
public section
noncomputable section
namespace LineSheafInverse318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
abbrev cocycle:=LineFrameCocycle318.cocycle M U frames
/-- The inverse is an actual clutched module, using inverses of the original
line's actual transition units. It is not labelled as a dual sheaf. -/
@[expose] def object:X.Modules:=
  CocycleModule318.object U (UnitCocycleInverse318.inverse (cocycle M U frames))
/-- Genuine whole-chart frames of the constructed inverse module. -/
@[expose] def frame (i:ι):SheafOfModules.unit (U i).toScheme.ringCatSheaf≅
    (object M U frames).restrict (U i).ι:=
  CocycleCanonicalTransitions318.frames U (UnitCocycleInverse318.inverse (cocycle M U frames)) i
lemma original_inverse_transitions:
    LineFrameCocycle318.cocycle (object M U frames) U (frame M U frames)=
      UnitCocycleInverse318.inverse (cocycle M U frames):=
  CocycleCanonicalTransitions318.cocycle_eq U _
@[expose] def rightFrames:=TensorLineCocycle318.frames M (object M U frames) U frames (frame M U frames)
@[expose] def leftFrames:=TensorLineCocycle318.frames (object M U frames) M U (frame M U frames) frames
lemma right_cocycle_one:
    LineFrameCocycle318.cocycle (tensor M (object M U frames)) U (rightFrames M U frames)=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U:=by
  rw [show LineFrameCocycle318.cocycle (tensor M (object M U frames)) U (rightFrames M U frames)=
    UnitCocycleProduct318.product (cocycle M U frames)
      (LineFrameCocycle318.cocycle (object M U frames) U (frame M U frames)) from
    TensorLineCocycle318.cocycle_eq M (object M U frames) U frames (frame M U frames)]
  rw [original_inverse_transitions,UnitCocycleInverse318.product_inverse]
lemma left_cocycle_one:
    LineFrameCocycle318.cocycle (tensor (object M U frames) M) U (leftFrames M U frames)=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units X).obj U:=by
  rw [show LineFrameCocycle318.cocycle (tensor (object M U frames) M) U (leftFrames M U frames)=
    UnitCocycleProduct318.product
      (LineFrameCocycle318.cocycle (object M U frames) U (frame M U frames)) (cocycle M U frames) from
    TensorLineCocycle318.cocycle_eq (object M U frames) M U (frame M U frames) frames]
  rw [original_inverse_transitions,UnitCocycleInverse318.inverse_product]
variable (hc:(⊤:X.Opens)≤⨆i,U i)
include hc in
lemma locallyFree:(object M U frames).IsLocallyFree:=
  CocycleActualLocalFrame318.locallyFree U _ hc
/-- Actual tensor cancellation, reconstructing the unchanged original tensor
from its original full-chart coefficient maps. -/
@[expose] def rightIso:tensor M (object M U frames)≅SheafOfModules.unit X.ringCatSheaf:=
  CocycleEqualityTransport318.changeTarget U
    (LineFrameReconstructionIso318.iso (tensor M (object M U frames)) U (rightFrames M U frames) hc)
    (right_cocycle_one M U frames) ≪≫ (StructureLineCocycleIso318.iso X U hc).symm
/-- The opposite tensor orientation uses its own actual frame comparison. -/
@[expose] def leftIso:tensor (object M U frames) M≅SheafOfModules.unit X.ringCatSheaf:=
  CocycleEqualityTransport318.changeTarget U
    (LineFrameReconstructionIso318.iso (tensor (object M U frames) M) U (leftFrames M U frames) hc)
    (left_cocycle_one M U frames) ≪≫ (StructureLineCocycleIso318.iso X U hc).symm
lemma right_hom_inv:(rightIso M U frames hc).hom≫(rightIso M U frames hc).inv=𝟙 _:=
  (rightIso M U frames hc).hom_inv_id
lemma right_inv_hom:(rightIso M U frames hc).inv≫(rightIso M U frames hc).hom=𝟙 _:=
  (rightIso M U frames hc).inv_hom_id
lemma left_hom_inv:(leftIso M U frames hc).hom≫(leftIso M U frames hc).inv=𝟙 _:=
  (leftIso M U frames hc).hom_inv_id
lemma left_inv_hom:(leftIso M U frames hc).inv≫(leftIso M U frames hc).hom=𝟙 _:=
  (leftIso M U frames hc).inv_hom_id
end LineSheafInverse318
