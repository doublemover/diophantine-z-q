module
public import PullbackFrameComposition318
public section
noncomputable section
namespace PullbackChartComposition318
open AlgebraicGeometry CategoryTheory
open PullbackPathComposition318
set_option maxHeartbeats 450000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z T:Scheme.{u}}
@[expose] def extend (f:X⟶Y) (j:Y⟶Z) (fj:X⟶Z) (h:f≫j=fj)
    (M:Z.Modules) (e:SheafOfModules.unit Y.ringCatSheaf≅(Scheme.Modules.pullback j).obj M):
    SheafOfModules.unit X.ringCatSheaf≅(Scheme.Modules.pullback fj).obj M:=
  PullbackFrameComposition318.frame f e≪≫(iso f j fj h).app M
lemma extend_assoc (f:X⟶Y) (g:Y⟶Z) (j:Z⟶T)
    (fg:X⟶Z) (gj:Y⟶T) (fgj:X⟶T)
    (hfg:f≫g=fg) (hgj:g≫j=gj) (hl:fg≫j=fgj) (hr:f≫gj=fgj)
    (M:T.Modules) (e:SheafOfModules.unit Z.ringCatSheaf≅(Scheme.Modules.pullback j).obj M):
    extend f gj fgj hr M (extend g j gj hgj M e)=extend fg j fgj hl M e:=by
  unfold extend
  rw [PullbackFrameComposition318.map_trans]
  apply Iso.ext
  simp only [Iso.trans_hom,Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,Category.assoc]
  rw [←PullbackPathComposition318.assoc f g j fg gj fgj hfg hgj hl hr M]
  have hh:=congrArg Iso.hom (PullbackFrameComposition318.composition f g fg hfg e)
  simpa only [Iso.trans_hom,Iso.app_hom,Category.assoc] using
    (congrArg (fun z=>z≫(iso fg j fgj hl).hom.app M) hh)
variable {A B C D E F:Scheme.{u}}
@[expose] def chart (p:A⟶B) (j:C⟶B) (k:D⟶A) (g:D⟶C)
    (t:D⟶B) (hkp:k≫p=t) (hgj:g≫j=t) (M:B.Modules)
    (e:SheafOfModules.unit C.ringCatSheaf≅(Scheme.Modules.pullback j).obj M):
    SheafOfModules.unit D.ringCatSheaf≅(Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback p).obj M):=
  extend g j t hgj M e≪≫((iso k p t hkp).app M).symm
lemma restrict_chart (p:A⟶B) (j:C⟶B) (k:D⟶A) (g:D⟶C)
    (t:D⟶B) (hkp:k≫p=t) (hgj:g≫j=t)
    (m:E⟶D) (mk:E⟶A) (mg:E⟶C) (total:E⟶B)
    (hmk:m≫k=mk) (hmg:m≫g=mg) (hmt:m≫t=total)
    (hkt:mk≫p=total) (hgt:mg≫j=total)
    (M:B.Modules) (e:SheafOfModules.unit C.ringCatSheaf≅(Scheme.Modules.pullback j).obj M):
    extend m k mk hmk ((Scheme.Modules.pullback p).obj M) (chart p j k g t hkp hgj M e)
      ≪≫(iso mk p total hkt).app M=
    extend mg j total hgt M e:=by
  unfold chart extend
  rw [PullbackFrameComposition318.map_trans]
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,Category.assoc]
  rw [PullbackPathComposition318.assoc m k p mk t total hmk hkp hkt hmt M]
  simp only [←Functor.map_comp_assoc,Iso.inv_hom_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
  have hh:=extend_assoc m g j mg t total hmg hgj hgt hmt M e
  exact congrArg Iso.hom hh
lemma nested (p:A⟶B) (j:C⟶B) (k:D⟶A) (g:D⟶C)
    (t:D⟶B) (hkp:k≫p=t) (hgj:g≫j=t)
    (m:E⟶D) (l:F⟶C) (q:E⟶F) (mk:E⟶A) (lj:F⟶B) (r:E⟶C) (total:E⟶B)
    (hmk:m≫k=mk) (hlj:l≫j=lj) (hmg:m≫g=r) (hql:q≫l=r)
    (hmt:m≫t=total) (hkt:mk≫p=total) (hrj:r≫j=total) (hqt:q≫lj=total)
    (M:B.Modules) (e:SheafOfModules.unit C.ringCatSheaf≅(Scheme.Modules.pullback j).obj M):
    extend m k mk hmk ((Scheme.Modules.pullback p).obj M) (chart p j k g t hkp hgj M e)=
      chart p lj mk q total hkt hqt M (extend l j lj hlj M e):=by
  apply Iso.ext
  apply (cancel_mono ((iso mk p total hkt).hom.app M)).mp
  have ha:=congrArg Iso.hom (restrict_chart p j k g t hkp hgj m mk r total
    hmk hmg hmt hkt hrj M e)
  have hb:=congrArg Iso.hom (extend_assoc q l j r lj total hql hlj hrj hqt M e)
  calc
    _=(extend r j total hrj M e).hom:=ha
    _=(extend q lj total hqt M (extend l j lj hlj M e)).hom:=hb.symm
    _=_:=by simp only [chart,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc,
      Iso.inv_hom_id_app,Category.comp_id]
end PullbackChartComposition318
