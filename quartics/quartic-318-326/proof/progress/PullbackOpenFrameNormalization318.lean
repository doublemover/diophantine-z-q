module
public import OpenFrameRestrictionComparison318
public import PullbackChartComposition318
public import LinePullbackFrames318
public section
noncomputable section
namespace PullbackOpenFrameNormalization318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
lemma restriction_congr {X Y:Scheme.{u}} {f g:X⟶Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h:f=g) (M:Y.Modules):
    (Scheme.Modules.restrictFunctorCongr h).hom.app M≫
      (Scheme.Modules.restrictFunctorIsoPullback g).hom.app M=
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M≫
      (Scheme.Modules.pullbackCongr h).hom.app M:=by
  subst g
  have hh:(Scheme.Modules.restrictFunctorCongr (rfl:f=f)).hom.app M=𝟙 _:=by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app,eqToHom_refl,
      op_id,CategoryTheory.Functor.map_id,Scheme.Modules.Hom.id_app]
    rfl
  rw [hh]
  simp only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app,
    Category.comp_id,Category.id_comp]
variable {X Y:Scheme.{u}} (f:X⟶Y) (M:Y.Modules) (U:Y.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
lemma chart_formula:
    LinePullbackFrames318.frame f M U e≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (f⁻¹ᵁU).ι).app ((Scheme.Modules.pullback f).obj M)=
    PullbackChartComposition318.chart f U.ι (f⁻¹ᵁU).ι (LinePullbackFrames318.chartMap f U)
      (LinePullbackFrames318.chartMap f U≫U.ι) (LinePullbackFrames318.square f U) rfl M
        (e≪≫(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M):=by
  apply Iso.ext
  simp only [LinePullbackFrames318.frame,PullbackLineFrames318.frame,
    PullbackLineFrames318.chartIso,PullbackChartComposition318.chart,
    PullbackChartComposition318.extend,PullbackFrameComposition318.frame,
    PullbackPathComposition318.iso,Iso.app_hom,Iso.app_inv,NatTrans.comp_app,Iso.trans_hom,Iso.symm_hom,Iso.trans_inv,
    Iso.symm_inv,Functor.mapIso_hom,Functor.mapIso_inv,Functor.map_comp,
    Category.assoc,Iso.inv_hom_id_app,Category.comp_id,Scheme.Modules.pullbackCongr,
    eqToIso_refl,Iso.refl_hom,Iso.refl_inv,NatTrans.id_app,Category.id_comp]
end PullbackOpenFrameNormalization318
