module
public import LineFrameAdjunction318
public import OpenLineFrameCoordinates318
public section
noncomputable section
namespace LineFrameChartCoordinates318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
lemma map_overFrame_inv:
    (Scheme.Modules.overEquiv U).functor.map (OpenLineSectionBasis318.overFrame M U e).inv=
      ((Scheme.Modules.overFunctorEquiv U).app M).hom≫e.inv:=by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      ((((U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫ e ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm)).inv))=_
  rw [Functor.map_preimage]
  simp only [Iso.trans_inv,Iso.symm_inv]
  rfl
lemma over_inv_app (W:U.toScheme.Opens) (s:Γ(M,U.ι ''ᵁW)):
    (OpenLineSectionBasis318.overFrame M U e).inv.val.app
      (op (Over.mk (homOfLE (show U.ι ''ᵁW≤U from by
        simpa using U.ι.image_le_opensRange W)))) s=
      e.inv.val.app (op W) s:=by
  have h:=congrArg (fun φ=>φ.val.app (op W) s) (map_overFrame_inv M U e)
  exact h
lemma image_preimage (W:X.Opens):U.ι ''ᵁ(U.ι⁻¹ᵁW)=U⊓W:=by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
@[expose] def ringIso (W:X.Opens):Γ(U.toScheme,U.ι⁻¹ᵁW)≅Γ(X,U⊓W):=
  X.presheaf.mapIso (eqToIso (image_preimage U W).symm).op
lemma ringIso_hom (W:X.Opens):
    (ringIso U W).hom=X.presheaf.map (homOfLE (image_preimage U W).symm.le).op:=by
  change X.presheaf.map _=X.presheaf.map _
  congr 1
lemma inverse_value (Z:X.Opens) (h:Z≤U) (s:Γ(M,Z)):
    (OpenLineFrameCoordinates318.frame M U e Z h).symm s=
      (OpenLineSectionBasis318.overFrame M U e).inv.val.app
        (op (Over.mk (homOfLE h))) s:=rfl
/-- Original line coordinates on an arbitrary ambient open, expressed in
exactly the original intersection section ring used by the cocycle. -/
lemma coordinate_app (W:X.Opens) (s:Γ(M,W)):
    (ringIso U W).hom ((LineFrameAdjunction318.coordinate M U e).app W s)=
      (OpenLineFrameCoordinates318.frame M U e (U⊓W) inf_le_left).symm
        (M.presheaf.map (homOfLE inf_le_right).op s):=by
  rw [LineFrameAdjunction318.coordinate_app]
  rw [←over_inv_app M U e (U.ι⁻¹ᵁW)]
  have h:=OpenLineFrameCoordinates318.inverse_natural M U e
    (show U.ι ''ᵁ(U.ι⁻¹ᵁW)≤U from by rw [image_preimage];exact inf_le_left)
    (show U⊓W≤U.ι ''ᵁ(U.ι⁻¹ᵁW) from (image_preimage U W).symm.le)
    (M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s)
  change _=(OpenLineFrameCoordinates318.frame M U e (U⊓W) inf_le_left).symm _ at h
  simp only [inverse_value,ringIso_hom,
    ←M.presheaf.map_comp_apply,←op_comp,homOfLE_comp] at h ⊢
  convert h using 1 <;> congr 2
end LineFrameChartCoordinates318
