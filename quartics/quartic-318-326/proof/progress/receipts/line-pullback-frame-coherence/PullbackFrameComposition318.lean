module
public import PullbackPathComposition318
public import PullbackUnitComposition318
public section
noncomputable section
namespace PullbackFrameComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z:Scheme.{u}}
@[expose] def frame (f:X⟶Y) {M:Y.Modules}
    (e:SheafOfModules.unit Y.ringCatSheaf≅M):
    SheafOfModules.unit X.ringCatSheaf≅(Scheme.Modules.pullback f).obj M:=
  (IdentityCotangent318.pullbackUnitIso f).symm≪≫(Scheme.Modules.pullback f).mapIso e
lemma map_trans (f:X⟶Y) {M N:Y.Modules}
    (e:SheafOfModules.unit Y.ringCatSheaf≅M) (a:M≅N):
    frame f (e≪≫a)=frame f e≪≫(Scheme.Modules.pullback f).mapIso a:=by
  apply Iso.ext
  simp only [frame,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Functor.map_comp,
    Category.assoc]
lemma composition (f:X⟶Y) (g:Y⟶Z) (fg:X⟶Z) (h:f≫g=fg)
    {M:Z.Modules} (e:SheafOfModules.unit Z.ringCatSheaf≅M):
    frame f (frame g e)≪≫(PullbackPathComposition318.iso f g fg h).app M=
      frame fg e:=by
  subst fg
  apply Iso.ext
  simp only [frame,PullbackPathComposition318.iso,Scheme.Modules.pullbackCongr,
    eqToIso_refl,Iso.trans_refl,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Functor.map_comp,Category.assoc]
  have hn:= (Scheme.Modules.pullbackComp f g).hom.naturality e.hom
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map e.hom)≫
    ((Scheme.Modules.pullbackComp f g).app M).hom=
    ((Scheme.Modules.pullbackComp f g).app _).hom≫
      (Scheme.Modules.pullback (f≫g)).map e.hom at hn
  rw [hn]
  change (IdentityCotangent318.pullbackUnitIso f).inv≫
    (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).inv≫
    (Scheme.Modules.pullbackComp f g).hom.app _≫(Scheme.Modules.pullback (f≫g)).map e.hom=_
  have hu:
      (IdentityCotangent318.pullbackUnitIso f).inv≫
      (Scheme.Modules.pullback f).map (IdentityCotangent318.pullbackUnitIso g).inv≫
      (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf)=
      (IdentityCotangent318.pullbackUnitIso (f≫g)).inv:=by
    apply (cancel_mono (IdentityCotangent318.pullbackUnitIso (f≫g)).hom).mp
    rw [Category.assoc,Category.assoc,PullbackUnitComposition318.composition]
    simp only [←Functor.map_comp_assoc,Iso.inv_hom_id,CategoryTheory.Functor.map_id,Category.id_comp,
      Iso.inv_hom_id]
  exact (congrArg (fun z=>z≫(Scheme.Modules.pullback (f≫g)).map e.hom) hu)
end PullbackFrameComposition318
