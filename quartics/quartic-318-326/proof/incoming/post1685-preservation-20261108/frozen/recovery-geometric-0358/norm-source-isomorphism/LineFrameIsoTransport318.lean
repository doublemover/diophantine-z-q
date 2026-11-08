module
public import LineFrameCocycle318
public section
noncomputable section
namespace LineFrameIsoTransport318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {M N:X.Modules} (e:M≅N) (U:X.Opens)
    (frame:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
/-- Transport the actual original frame by the actual original module iso. -/
@[expose] def transported:SheafOfModules.unit U.toScheme.ringCatSheaf≅N.restrict U.ι:=
  frame≪≫(Scheme.Modules.restrictFunctor U.ι).mapIso e
lemma overFrame_image:
    (Scheme.Modules.overEquiv U).functor.map (OpenLineSectionBasis318.overFrame M U frame).hom=
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom≫frame.hom≫
        ((Scheme.Modules.overFunctorEquiv U).app M).inv:=by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf)≪≫frame≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm).hom)=_
  rw [Functor.map_preimage]
  rfl
lemma overFrame_transport:
    (OpenLineSectionBasis318.overFrame N U (transported e U frame)).hom=
      (OpenLineSectionBasis318.overFrame M U frame).hom≫
        (SheafOfModules.overFunctor X.ringCatSheaf U).map e.hom:=by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  rw [Functor.map_comp,overFrame_image,overFrame_image]
  change (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom≫
      (frame.hom≫(Scheme.Modules.restrictFunctor U.ι).map e.hom)≫
        ((Scheme.Modules.overFunctorEquiv U).app N).inv=
    ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom≫frame.hom≫
      ((Scheme.Modules.overFunctorEquiv U).app M).inv)≫_
  simp only [Category.assoc]
  exact congrArg (fun f=>(U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom≫frame.hom≫f)
    ((Scheme.Modules.overFunctorEquiv U).inv.naturality e.hom)
lemma coordinates (W:X.Opens) (h:W≤U) (s:Γ(X,W)):
    OpenLineFrameCoordinates318.frame N U (transported e U frame) W h s=
      e.hom.app W (OpenLineFrameCoordinates318.frame M U frame W h s):=by
  have he:=congrArg (fun f=>f.val.app (op (Over.mk (homOfLE h))) s)
    (overFrame_transport e U frame)
  exact he
lemma inverse_coordinates (W:X.Opens) (h:W≤U) (s:Γ(M,W)):
    (OpenLineFrameCoordinates318.frame N U (transported e U frame) W h).symm
      (e.hom.app W s)=
        (OpenLineFrameCoordinates318.frame M U frame W h).symm s:=by
  apply (OpenLineFrameCoordinates318.frame N U (transported e U frame) W h).injective
  rw [LinearEquiv.apply_symm_apply,coordinates,LinearEquiv.apply_symm_apply]
end LineFrameIsoTransport318
