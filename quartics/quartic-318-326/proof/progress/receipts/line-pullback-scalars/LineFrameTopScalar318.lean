module
public import LineFrameChartCoordinates318
public import LineFrameTransitions318
public import UnitSheafScalar318
public section
noncomputable section
namespace LineFrameTopScalar318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
lemma image_top:U.ι ''ᵁ(⊤:U.toScheme.Opens)=U:=by
  rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
@[expose] def ringTop:Γ(U.toScheme,⊤)≅Γ(X,U):=
  X.presheaf.mapIso (eqToIso (image_top U).symm).op
lemma ringTop_hom:
    (ringTop U).hom=X.presheaf.map (homOfLE (image_top U).symm.le).op:=by
  change X.presheaf.map _=X.presheaf.map _
  congr 1
variable (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
lemma map_overFrame_hom:
    (Scheme.Modules.overEquiv U).functor.map (OpenLineSectionBasis318.overFrame M U e).hom=
      e.hom≫((Scheme.Modules.overFunctorEquiv U).app M).inv:=by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      ((((U.sheafOfModulesEquivOverUnit X.ringCatSheaf)≪≫e≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm)).hom))=_
  rw [Functor.map_preimage]
  simp only [Iso.trans_hom,Iso.symm_hom]
  rfl
lemma over_hom_app (W:U.toScheme.Opens) (s:Γ(U.toScheme,W)):
    (OpenLineSectionBasis318.overFrame M U e).hom.val.app
      (op (Over.mk (homOfLE (show U.ι ''ᵁW≤U from by
        simpa using U.ι.image_le_opensRange W)))) s=
      e.hom.val.app (op W) s:=by
  have h:=congrArg (fun φ=>φ.val.app (op W) s) (map_overFrame_hom M U e)
  exact h
/-- Exact original-open scalar compared with the same actual frame
composition on the open subscheme, using the genuine ring comparison. -/
lemma scalar (e0 e1:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι):
    Units.map (ringTop U).hom.hom.toMonoidHom
      (UnitSheafScalar318.unit (e1≪≫e0.symm))=
    FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame M U e0 U le_rfl)
      (OpenLineFrameCoordinates318.frame M U e1 U le_rfl):=by
  apply Units.ext
  change (ringTop U).hom
    ((e0.inv.val.app (op (⊤:U.toScheme.Opens)))
      ((e1.hom.val.app (op (⊤:U.toScheme.Opens))) (1:Γ(U.toScheme,⊤))))=_
  rw [←over_hom_app M U e1,←LineFrameChartCoordinates318.over_inv_app M U e0]
  have h:=OpenLineFrameCoordinates318.inverse_natural M U e0
    (show U.ι ''ᵁ(⊤:U.toScheme.Opens)≤U from (image_top U).le)
    (image_top U).symm.le
    (OpenLineFrameCoordinates318.frame M U e1 (U.ι ''ᵁ(⊤:U.toScheme.Opens))
      (image_top U).le 1)
  rw [OpenLineFrameCoordinates318.natural] at h
  simp only [map_one] at h
  exact h
end LineFrameTopScalar318
