module
public import OpenLineFrameRefinement318
public import LineFrameChartCoordinates318
public section
noncomputable section
namespace OpenFrameRestrictionComparison318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (W:X.Opens) (h:W≤U)
lemma image_eq (Z:W.toScheme.Opens):
    U.ι ''ᵁ((X.homOfLE h) ''ᵁZ)=W.ι ''ᵁZ:=by
  simpa only [Scheme.homOfLE_ι] using (Scheme.Hom.comp_image (X.homOfLE h) U.ι Z).symm
lemma original_formula (Z:W.toScheme.Opens) (s:Γ(W.toScheme,Z)):
    (OpenLineSectionBasis318.restrictFrame M U e W h).hom.val.app (op Z) s=
      M.presheaf.map (homOfLE (image_eq U W h Z).symm.le).op
        (e.hom.val.app (op ((X.homOfLE h) ''ᵁZ)) ((X.homOfLE h).appIso Z |>.inv <| s)):=by
  simp only [OpenLineSectionBasis318.restrictFrame,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom]
  change M.presheaf.map _ (M.presheaf.map _
    (e.hom.val.app (op ((X.homOfLE h) ''ᵁZ)) ((X.homOfLE h).appIso Z |>.inv <| s)))=_
  rw [←M.presheaf.map_comp_apply]
  rfl
lemma map_overFrame_hom:
    (Scheme.Modules.overEquiv U).functor.map (OpenLineSectionBasis318.overFrame M U e).hom=
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom≫e.hom≫
        ((Scheme.Modules.overFunctorEquiv U).app M).inv:=by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫e≪≫
        ((Scheme.Modules.overFunctorEquiv U).app M).symm).hom)=_
  rw [Functor.map_preimage]
  rfl
lemma over_hom_app (T:U.toScheme.Opens) (s:Γ(U.toScheme,T)):
    (OpenLineSectionBasis318.overFrame M U e).hom.val.app
      (op (Over.mk (homOfLE (show U.ι ''ᵁT≤U from by simpa using U.ι.image_le_opensRange T)))) s=
      e.hom.val.app (op T) s:=by
  exact congrArg (fun φ=>φ.val.app (op T) s) (map_overFrame_hom M U e)
lemma refined_formula (Z:W.toScheme.Opens) (s:Γ(W.toScheme,Z)):
    (OpenLineFrameRefinement318.frame M U e W h).hom.val.app (op Z) s=
      (OpenLineSectionBasis318.overFrame M U e).hom.val.app
        (op (Over.mk (homOfLE ((show W.ι ''ᵁZ≤W from by simpa using W.ι.image_le_opensRange Z).trans h)))) s:=rfl
lemma ring_formula (Z:W.toScheme.Opens) (s:Γ(W.toScheme,Z)):
    ((X.homOfLE h).appIso Z |>.inv <| s)=
      X.presheaf.map (homOfLE (image_eq U W h Z).le).op s:=by
  have hh:=congrArg (fun q=>q s) (Scheme.Hom.appIso_homOfLE_inv h Z)
  exact hh
lemma frame_eq:
    OpenLineFrameRefinement318.frame M U e W h=OpenLineSectionBasis318.restrictFrame M U e W h:=by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro Z
  ext s
  let I₁:=U.ι ''ᵁ((X.homOfLE h) ''ᵁZ)
  let I₂:=W.ι ''ᵁZ
  have h₁:I₁≤U:=by simpa [I₁] using U.ι.image_le_opensRange ((X.homOfLE h) ''ᵁZ)
  have h₂:I₂≤U:=(show W.ι ''ᵁZ≤W from by simpa using W.ι.image_le_opensRange Z).trans h
  let q:Over.mk (homOfLE h₂)⟶Over.mk (homOfLE h₁):=
    Over.homMk (homOfLE (image_eq U W h Z).symm.le)
  have hn:=PresheafOfModules.naturality_apply (OpenLineSectionBasis318.overFrame M U e).hom.val q.op
    (X.presheaf.map (homOfLE (image_eq U W h Z).le).op s)
  change (OpenLineSectionBasis318.overFrame M U e).hom.val.app (op (Over.mk (homOfLE h₂)))
      (X.presheaf.map (homOfLE (image_eq U W h Z).symm.le).op
        (X.presheaf.map (homOfLE (image_eq U W h Z).le).op s))=
    M.presheaf.map (homOfLE (image_eq U W h Z).symm.le).op
      ((OpenLineSectionBasis318.overFrame M U e).hom.val.app (op (Over.mk (homOfLE h₁)))
        (X.presheaf.map (homOfLE (image_eq U W h Z).le).op s)) at hn
  simp only [←X.presheaf.map_comp_apply,←op_comp,homOfLE_comp,homOfLE_refl,op_id,
    CategoryTheory.Functor.map_id] at hn
  have ha:=over_hom_app M U e ((X.homOfLE h) ''ᵁZ) ((X.homOfLE h).appIso Z |>.inv <| s)
  have hb:=congrArg (fun z=>(OpenLineSectionBasis318.overFrame M U e).hom.val.app
    (op (Over.mk (homOfLE h₁))) z) (ring_formula U W h Z s)
  exact (refined_formula M U e W h Z s).trans
    (hn.trans ((congrArg (fun z=>M.presheaf.map (homOfLE (image_eq U W h Z).symm.le).op z)
      (hb.symm.trans ha)).trans (original_formula M U e W h Z s).symm))
end OpenFrameRestrictionComparison318
