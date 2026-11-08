module
public import CocycleCanonicalTransitions318
public import CocycleEqualityTransport318
public import OpenLineFrameRefinement318
public import LineFrameReconstructionIso318
public section
noncomputable section
namespace CocycleRefinementIso318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι κ:Type u} (U:ι→X.Opens)
    (c:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (W:κ→X.Opens) (r:κ→ι) (hr:∀k,W k≤U (r k))
abbrev M:=CocycleModule318.object U c
@[expose] def frames (k:κ):SheafOfModules.unit (W k).toScheme.ringCatSheaf≅
    (M U c).restrict (W k).ι:=
  OpenLineFrameRefinement318.refinedFrames (M U c) U
    (CocycleCanonicalTransitions318.frames U c) W r hr k
lemma extracted:
    LineFrameCocycle318.cocycle (M U c) W (frames U c W r hr)=
      UnitCocycleRefinement318.refine c W r hr:=by
  change LineFrameCocycle318.cocycle (M U c) W
    (OpenLineFrameRefinement318.refinedFrames (M U c) U
      (CocycleCanonicalTransitions318.frames U c) W r hr)=_
  rw [OpenLineFrameRefinement318.extracted_refine,CocycleCanonicalTransitions318.cocycle_eq]
variable (hW:(⊤:X.Opens)≤⨆k,W k)
/-- Actual refinement of the original cocycle sheaf. Only the refined
family is assumed covering; no different sheaf or pointwise replacement is used. -/
@[expose] def iso:M U c≅CocycleModule318.object W (UnitCocycleRefinement318.refine c W r hr):=
  CocycleEqualityTransport318.changeTarget W
    (LineFrameReconstructionIso318.iso (M U c) W (frames U c W r hr) hW)
    (extracted U c W r hr)
lemma hom_inv:(iso U c W r hr hW).hom≫(iso U c W r hr hW).inv=𝟙 _:=
  (iso U c W r hr hW).hom_inv_id
lemma inv_hom:(iso U c W r hr hW).inv≫(iso U c W r hr hW).hom=𝟙 _:=
  (iso U c W r hr hW).inv_hom_id
lemma hom_coefficient (k:κ):
    (iso U c W r hr hW).hom≫
      CocycleModule318.coefficient W (UnitCocycleRefinement318.refine c W r hr) k=
        LineFrameAdjunction318.coordinate (M U c) (W k) (frames U c W r hr k):=by
  exact (CocycleEqualityTransport318.changeTarget_coefficient W
    (LineFrameReconstructionIso318.iso (M U c) W (frames U c W r hr) hW)
    (extracted U c W r hr) k).trans
      (LineFrameReconstructionIso318.hom_coefficient (M U c) W (frames U c W r hr) hW k)
lemma inv_coordinate (k:κ):
    (iso U c W r hr hW).inv≫
      LineFrameAdjunction318.coordinate (M U c) (W k) (frames U c W r hr k)=
        CocycleModule318.coefficient W (UnitCocycleRefinement318.refine c W r hr) k:=by
  rw [←hom_coefficient U c W r hr hW k,←Category.assoc,inv_hom,Category.id_comp]
lemma original_frame (k:κ):
    (Scheme.Modules.restrictFunctor (W k).ι).map (iso U c W r hr hW).hom≫
      CocycleActualLocalFrame318.transpose W (UnitCocycleRefinement318.refine c W r hr) k=
        (frames U c W r hr k).inv:=by
  change (Scheme.Modules.restrictFunctor (W k).ι).map (iso U c W r hr hW).hom≫
    ((Scheme.Modules.restrictAdjunction (W k).ι).homEquiv _ _).symm
      (CocycleModule318.coefficient W (UnitCocycleRefinement318.refine c W r hr) k)=_
  rw [←Adjunction.homEquiv_naturality_left_symm,hom_coefficient,
    LineFrameAdjunction318.transpose]
end CocycleRefinementIso318
