module
public import TensorLineCocycle318
public import CocycleCanonicalTransitions318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace CocycleTensorIso318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
set_option maxHeartbeats 150000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
abbrev left:X.Modules:=CocycleModule318.object U c
abbrev right:X.Modules:=CocycleModule318.object U d
@[expose] def frames (i:ι):SheafOfModules.unit (U i).toScheme.ringCatSheaf≅
    (tensor (left U c) (right U d)).restrict (U i).ι:=
  TensorLineCocycle318.frames (left U c) (right U d) U
    (CocycleCanonicalTransitions318.frames U c) (CocycleCanonicalTransitions318.frames U d) i
lemma tensor_cocycle:
    LineFrameCocycle318.cocycle (tensor (left U c) (right U d)) U (frames U c d)=
      UnitCocycleProduct318.product c d:=by
  rw [show LineFrameCocycle318.cocycle (tensor (left U c) (right U d)) U (frames U c d)=
    UnitCocycleProduct318.product
      (LineFrameCocycle318.cocycle (left U c) U (CocycleCanonicalTransitions318.frames U c))
      (LineFrameCocycle318.cocycle (right U d) U (CocycleCanonicalTransitions318.frames U d)) from
    TensorLineCocycle318.cocycle_eq (left U c) (right U d) U _ _]
  rw [CocycleCanonicalTransitions318.cocycle_eq,CocycleCanonicalTransitions318.cocycle_eq]
variable (hc:(⊤:X.Opens)≤⨆i,U i)
/-- The actual tensor of the two unchanged cocycle modules is reconstructed
from its genuine local tensor frames, then identified by the proved original
transition equality. Both inverse maps are genuine categorical inverses. -/
@[expose] def iso:tensor (left U c) (right U d)≅
    CocycleModule318.object U (UnitCocycleProduct318.product c d):=
  LineFrameReconstructionIso318.iso (tensor (left U c) (right U d)) U (frames U c d) hc ≪≫
    eqToIso (congrArg (CocycleModule318.object U) (tensor_cocycle U c d))
lemma hom_inv:(iso U c d hc).hom≫(iso U c d hc).inv=𝟙 _ :=(iso U c d hc).hom_inv_id
lemma inv_hom:(iso U c d hc).inv≫(iso U c d hc).hom=𝟙 _ :=(iso U c d hc).inv_hom_id
end CocycleTensorIso318
