module
public import PullbackOpenFrameNormalization318
public import RestrictionPullbackCoherence318
public section
noncomputable section
namespace OpenFramePullbackRestriction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
lemma composition_inverse {X Y Z:Scheme.{u}} (f:X⟶Y) (g:Y⟶Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M:Z.Modules):
    (Scheme.Modules.restrictFunctorComp f g).inv.app M≫
      (Scheme.Modules.restrictFunctorIsoPullback (f≫g)).hom.app M=
    (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M)≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M)≫
      (Scheme.Modules.pullbackComp f g).hom.app M:=by
  apply (cancel_mono ((Scheme.Modules.pullbackComp f g).inv.app M)).mp
  simp only [Category.assoc,Iso.hom_inv_id_app,Category.comp_id]
  rw [RestrictionPullbackCoherence318.composition]
  simp only [Iso.inv_hom_id_app_assoc,Category.comp_id]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  rfl
@[reassoc] lemma unit_inverse {X Y:Scheme.{u}} (f:X⟶Y) [IsOpenImmersion f]:
    (Scheme.Modules.restrictUnitIso f).inv≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf)=
      (IdentityCotangent318.pullbackUnitIso f).inv:=by
  apply (cancel_mono (IdentityCotangent318.pullbackUnitIso f).hom).mp
  rw [Category.assoc,RestrictionPullbackCoherence318.restrict_unit]
  simp only [Iso.inv_hom_id]
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (W:X.Opens) (h:W≤U)
lemma normalized:
    OpenLineFrameRefinement318.frame M U e W h≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M=
    PullbackChartComposition318.extend (X.homOfLE h) U.ι W.ι (Scheme.homOfLE_ι X h) M
      (e≪≫(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M):=by
  rw [OpenFrameRestrictionComparison318.frame_eq]
  apply Iso.ext
  simp only [OpenLineSectionBasis318.restrictFrame,PullbackChartComposition318.extend,
    PullbackFrameComposition318.frame,PullbackPathComposition318.iso,Iso.trans_hom,
    Iso.symm_hom,Iso.app_hom,Iso.app_inv,Functor.mapIso_hom,Category.assoc]
  rw [PullbackOpenFrameNormalization318.restriction_congr]
  rw [←Category.assoc ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).inv.app M),
    composition_inverse]
  simp only [Category.assoc]
  have hn: (Scheme.Modules.restrictFunctor (X.homOfLE h)).map e.hom≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M)≫
      (Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).hom.app
        ((Scheme.Modules.pullback U.ι).obj M)=
    (Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).hom.app
      (SheafOfModules.unit U.toScheme.ringCatSheaf)≫
      (Scheme.Modules.pullback (X.homOfLE h)).map
        (e.hom≫(Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M):=by
    rw [←Category.assoc,←Functor.map_comp]
    exact (Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE h)).hom.naturality _
  have ha:=congrArg (fun z=>(Scheme.Modules.restrictUnitIso (X.homOfLE h)).inv≫z≫
    (Scheme.Modules.pullbackComp (X.homOfLE h) U.ι).hom.app M≫
      (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι X h)).hom.app M) hn
  simpa only [Category.assoc,unit_inverse_assoc,Functor.map_comp,NatTrans.comp_app] using ha
end OpenFramePullbackRestriction318
