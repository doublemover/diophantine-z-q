module
public import TensorLineCocycle318
public import TensorLineCoordinateMaps318
public import CocycleCanonicalTransitions318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace CocycleTensorIso318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
    (c d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
abbrev left:=CocycleModule318.object U c
abbrev right:=CocycleModule318.object U d
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
lemma coefficient_cast {a b:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U}
    (h:a=b) (i:ι):
    (eqToIso (congrArg (CocycleModule318.object U) h)).hom≫CocycleModule318.coefficient U b i=
      CocycleModule318.coefficient U a i:=by
  subst b
  simp
lemma transpose_cast {a b:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U}
    (h:a=b) (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map
      (eqToIso (congrArg (CocycleModule318.object U) h)).hom≫CocycleActualLocalFrame318.transpose U b i=
      CocycleActualLocalFrame318.transpose U a i:=by
  subst b
  simp
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
lemma hom_coefficient (i:ι):
    (iso U c d hc).hom≫CocycleModule318.coefficient U (UnitCocycleProduct318.product c d) i=
      LineFrameAdjunction318.coordinate (tensor (left U c) (right U d)) (U i) (frames U c d i):=by
  rw [iso,Iso.trans_hom,Category.assoc,coefficient_cast]
  exact LineFrameReconstructionIso318.hom_coefficient _ _ _ _ i
/-- The exact local coefficient transpose agrees with the original tensor
frame inverse, not merely with some local rank-one isomorphism. -/
lemma hom_frame (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map (iso U c d hc).hom≫
      CocycleActualLocalFrame318.transpose U (UnitCocycleProduct318.product c d) i=(frames U c d i).inv:=by
  rw [iso,Iso.trans_hom,Functor.map_comp,Category.assoc,transpose_cast]
  exact LineFrameReconstructionIso318.original_frame _ _ _ _ i
lemma inv_frame (i:ι):
    (Scheme.Modules.restrictFunctor (U i).ι).map (iso U c d hc).inv≫(frames U c d i).inv=
      CocycleActualLocalFrame318.transpose U (UnitCocycleProduct318.product c d) i:=by
  rw [←hom_frame U c d hc i,←Category.assoc,←Functor.map_comp,inv_hom,Functor.map_id,Category.id_comp]
/-- Every actual original coefficient of an ambient pure tensor is exactly
the product of its two original coefficient sections. -/
lemma pure_coefficient (i:ι) (W:X.Opens) (m:Γ(left U c,W)) (n:Γ(right U d,W)):
    (CocycleModule318.coefficient U (UnitCocycleProduct318.product c d) i).val.app (op W)
      ((iso U c d hc).hom.val.app (op W) (pure (left U c) (right U d) W m n))=
      ((CocycleModule318.coefficient U c i).val.app (op W) m:Γ((U i).toScheme,(U i).ι⁻¹ᵁW))*
        ((CocycleModule318.coefficient U d i).val.app (op W) n:Γ((U i).toScheme,(U i).ι⁻¹ᵁW)):=by
  have h:=congrArg (fun q=>Scheme.Modules.Hom.app q W (pure (left U c) (right U d) W m n))
    (hom_coefficient U c d hc i)
  change (CocycleModule318.coefficient U (UnitCocycleProduct318.product c d) i).val.app (op W)
    ((iso U c d hc).hom.val.app (op W) (pure (left U c) (right U d) W m n))=
      (LineFrameAdjunction318.coordinate (tensor (left U c) (right U d)) (U i) (frames U c d i)).val.app (op W)
        (pure (left U c) (right U d) W m n) at h
  rw [h]
  change (LineFrameAdjunction318.coordinate (tensor (left U c) (right U d)) (U i)
    (TensorLineLocalFrame318.frame (left U c) (right U d) (U i)
      (CocycleCanonicalTransitions318.frames U c i) (CocycleCanonicalTransitions318.frames U d i))).val.app (op W)
      (pure (left U c) (right U d) W m n)=_
  rw [TensorLineCoordinateMaps318.coordinate_pure,CocycleCanonicalTransitions318.coordinate,
    CocycleCanonicalTransitions318.coordinate]
end CocycleTensorIso318
