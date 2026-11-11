module
public import OpenLineFrameCoordinates318
public import LineFrameCocycle318
public import UnitCocycleRefinement318
public section
noncomputable section
namespace OpenLineFrameRefinement318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
/-- Transport a genuine frame on the original over-open site back to the
actual open subscheme, through the canonical equivalence and comparison. -/
@[expose] def fromOver (g:SheafOfModules.unit (X.ringCatSheaf.over U)≅M.over U):
    SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι:=
  (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso g ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
lemma over_fromOver (g:SheafOfModules.unit (X.ringCatSheaf.over U)≅M.over U):
    OpenLineSectionBasis318.overFrame M U (fromOver M U g)=g:=by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫ fromOver M U g ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm).hom)=_
  rw [Functor.map_preimage]
  simp only [fromOver,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Category.assoc,
    Iso.hom_inv_id_assoc,Iso.inv_hom_id_assoc,Iso.hom_inv_id,Category.comp_id]
variable (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (W:X.Opens) (h:W≤U)
/-- The genuine restriction of the same original frame on the over-open site. -/
@[expose] def overRestriction:SheafOfModules.unit (X.ringCatSheaf.over W)≅M.over W:=
  (SheafOfModules.overMapUnitIso (R:=X.ringCatSheaf) (homOfLE h)).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso (OpenLineSectionBasis318.overFrame M U e) ≪≫
      (SheafOfModules.overFunctorMap (R:=X.ringCatSheaf) (homOfLE h)).app M
@[expose] def frame:SheafOfModules.unit W.toScheme.ringCatSheaf≅M.restrict W.ι:=
  fromOver M W (overRestriction M U e W h)
lemma coordinates (Z:X.Opens) (hZ:Z≤W):
    OpenLineFrameCoordinates318.frame M W (frame M U e W h) Z hZ=
      OpenLineFrameCoordinates318.frame M U e Z (hZ.trans h):=by
  unfold OpenLineFrameCoordinates318.frame frame
  rw [over_fromOver]
  rfl
variable {ι:Type v} {κ:Type w} (V:ι→X.Opens)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
    (T:κ→X.Opens) (r:κ→ι) (hr:∀k,T k≤V (r k))
@[expose] def refinedFrames (k:κ):SheafOfModules.unit (T k).toScheme.ringCatSheaf≅M.restrict (T k).ι:=
  frame M (V (r k)) (frames (r k)) (T k) (hr k)
/-- Exact extracted cocycle equality, not just gauge equivalence. -/
lemma extracted_refine:
    LineFrameCocycle318.cocycle M T (refinedFrames M V frames T r hr)=
      UnitCocycleRefinement318.refine (LineFrameCocycle318.cocycle M V frames) T r hr:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  change FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame M (T i) (refinedFrames M V frames T r hr i) _ inf_le_left)
    (OpenLineFrameCoordinates318.frame M (T j) (refinedFrames M V frames T r hr j) _ inf_le_right)=_
  simp only [refinedFrames,coordinates]
  exact (LineFrameTransitions318.restrict M V frames (r i) (r j) inf_le_left inf_le_right
    (inf_le_inf (hr i) (hr j))).symm
end OpenLineFrameRefinement318
