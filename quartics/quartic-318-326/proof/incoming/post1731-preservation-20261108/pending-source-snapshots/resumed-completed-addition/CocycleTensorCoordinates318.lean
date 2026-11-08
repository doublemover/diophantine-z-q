module
public import CocycleTensorIso318
public import TensorLineCoordinateMaps318
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
      (fun a b:Γ((U i).toScheme,(U i).ι⁻¹ᵁW)=>a*b)
        ((CocycleModule318.coefficient U c i).val.app (op W) m)
        ((CocycleModule318.coefficient U d i).val.app (op W) n):=by
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
