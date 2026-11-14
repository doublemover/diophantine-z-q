module
public import PullbackChartNaturality318
public section
noncomputable section
namespace PullbackPathComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z T:Scheme.{u}}
@[expose] def iso (f:X⟶Y) (g:Y⟶Z) (fg:X⟶Z) (h:f≫g=fg):
    Scheme.Modules.pullback g⋙Scheme.Modules.pullback f≅Scheme.Modules.pullback fg:=
  Scheme.Modules.pullbackComp f g ≪≫Scheme.Modules.pullbackCongr h
lemma assoc (f:X⟶Y) (g:Y⟶Z) (h:Z⟶T)
    (fg:X⟶Z) (gh:Y⟶T) (fgh:X⟶T)
    (hfg:f≫g=fg) (hgh:g≫h=gh) (hl:fg≫h=fgh) (hr:f≫gh=fgh) (M:T.Modules):
    (iso f g fg hfg).hom.app ((Scheme.Modules.pullback h).obj M)≫
      (iso fg h fgh hl).hom.app M=
    (Scheme.Modules.pullback f).map ((iso g h gh hgh).hom.app M)≫
      (iso f gh fgh hr).hom.app M:=by
  subst fg
  subst gh
  subst fgh
  simp only [iso,Iso.trans_hom,NatTrans.comp_app,Scheme.Modules.pullbackCongr,
    eqToIso_refl,Iso.refl_hom,NatTrans.id_app,Category.comp_id]
  apply (cancel_epi ((Scheme.Modules.pullbackComp f (g≫h)).inv.app M≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M))).mp
  have hh:=congrArg (fun α=>α.app M) (Scheme.Modules.pseudofunctor_associativity f g h)
  simpa only [NatTrans.comp_app,Functor.whiskerRight_app,Functor.whiskerLeft_app,
    Functor.associator_hom_app,Category.id_comp,Category.assoc,
    ←Functor.map_comp_assoc,Iso.inv_hom_id_app,CategoryTheory.Functor.map_id,
    Iso.inv_hom_id_app_assoc,eqToHom_refl,NatTrans.id_app] using hh
end PullbackPathComposition318
