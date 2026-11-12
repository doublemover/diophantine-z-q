module
public import LocalPullbackUnit318
public import PullbackLineFrames318
public import PullbackAdjointUnitFrame318
public import OpenFrameRestrictionComparison318
public import LinePullbackFrames318
public section
noncomputable section
namespace LocalPullbackFrameGenerator318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The equal-arrow comparison is an actual mate, including its original
pushforward comparison. This equality is on whole module sheaves. -/
lemma congr_adjoint {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f=g)
    (M : Y.Modules) (N : X.Modules) (q : (Scheme.Modules.pullback g).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullbackCongr h).hom.app M ≫ q) ≫
      (Scheme.Modules.pushforwardCongr h).hom.app N=
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ q := by
  subst g
  have hp : (Scheme.Modules.pushforwardCongr (rfl : f=f)).hom.app N=𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app,eqToHom_refl,
      op_id,Functor.map_id,Scheme.Modules.Hom.id_app]
  rw [hp]
  simp only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,
    NatTrans.id_app,Category.id_comp,Category.comp_id]

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) (k : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] (g : V ⟶ U) (h : k≫f=g≫j)
  (M : Y.Modules)
local notation "N" => (Scheme.Modules.pullback g).obj (M.restrict j)

/-- Exact mate of the EXISTING five-factor chart comparison. Evaluating
this equality at ANY base open gives the local-section normalization;
no local section is presumed to extend to a global section. -/
lemma chart_mate :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction k).homEquiv _ _
        (PullbackLineFrames318.chartIso f j k g h M).hom) ≫
      (Scheme.Modules.pushforwardComp k f).hom.app N ≫
      (Scheme.Modules.pushforwardCongr h).hom.app N=
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (M.restrict j)) ≫
      (Scheme.Modules.pushforwardComp g j).hom.app N := by
  let q : ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback f).obj M)) ⟶ N :=
    (Scheme.Modules.pullbackComp k f).hom.app M ≫
      (Scheme.Modules.pullbackCongr h).hom.app M ≫
      (Scheme.Modules.pullbackComp g j).inv.app M ≫
      (Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M)
  have hc : (PullbackLineFrames318.chartIso f j k g h M).hom=
      (Scheme.Modules.restrictFunctorIsoPullback k).hom.app
        ((Scheme.Modules.pullback f).obj M) ≫ q := by
    simp only [PullbackLineFrames318.chartIso,Iso.trans_hom,Iso.app_hom,
      Iso.app_inv,Iso.symm_hom,Functor.mapIso_hom,Category.assoc,q]
  rw [hc,RestrictionPullbackCoherence318.adjoint_restrict]
  have hm := PullbackUnitComposition318.homEquiv_mate
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction k))
    (Scheme.Modules.pullbackPushforwardAdjunction (k≫f))
    (Scheme.Modules.pullbackComp k f).inv q
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv,Adjunction.comp_homEquiv] at hm
  rw [←Category.assoc,←hm]
  simp only [q,Category.assoc,Iso.inv_hom_id_app_assoc]
  rw [congr_adjoint]
  rw [PullbackUnitComposition318.homEquiv_mate
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,Adjunction.comp_homEquiv]
  congr 1
  have hg : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M))=
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app M ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (M.restrict j) := by
    rw [Adjunction.homEquiv_unit]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M)).symm
  rw [hg]
  have hj := RestrictionPullbackCoherence318.adjoint_restrict j
    (((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (M.restrict j))
  simpa only [Category.assoc,Iso.hom_inv_id_app_assoc] using hj.symm

/-- The actual five-factor chart map carries a pulled ARBITRARY local
section to the pulled restriction of that same section. The canonical
open-equality transport is explicit, so no change of source open is
silently treated as definitional equality. -/
lemma chart_local_unit (W : Y.Opens) (s : Γ(M,W)) :
    ((Scheme.Modules.pushforwardCongr h).hom.app N).app W
      ((PullbackLineFrames318.chartIso f j k g h M).hom.app (k⁻¹ᵁ(f⁻¹ᵁW))
        (((Scheme.Modules.pullback f).obj M).presheaf.map
          (homOfLE (k.image_preimage_le (f⁻¹ᵁW))).op
          (LocalPullbackUnit318.pull f M W s)))=
    LocalPullbackUnit318.pull g (M.restrict j) (j⁻¹ᵁW)
      (M.presheaf.map (homOfLE (j.image_preimage_le W)).op s) := by
  have hm := congrArg (fun q => q.app W s) (chart_mate f j k g h M)
  simpa only [Adjunction.homEquiv_unit,Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app,Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app] using hm

/-- Restrict the actual ambient frame generator to the inverse-image
chart open. This uses the original over-site frame, not a replacement. -/
lemma ambient_generator {Z : Scheme.{u}} (B : Z.Modules) (W : Z.Opens)
    (e : SheafOfModules.unit W.toScheme.ringCatSheaf ≅ B.restrict W.ι) :
    B.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op
      (OpenLineFrameCoordinates318.frame B W e W le_rfl 1)=
    e.hom.app (W.ι⁻¹ᵁW) 1 := by
  have hn := OpenLineFrameCoordinates318.natural B W e
    (hZ := le_rfl) (hWZ := W.ι.image_preimage_le W) (1 : Γ(Z,W))
  have he := OpenFrameRestrictionComparison318.over_hom_app B W e
    (W.ι⁻¹ᵁW) (1 : Γ(W.toScheme,W.ι⁻¹ᵁW))
  simp only [map_one] at hn
  simpa only [OpenLineFrameCoordinates318.frame] using hn.trans he

lemma congr_generator {Z T : Scheme.{u}} {a b : Z ⟶ T} (hab : a=b)
    (B : Z.Modules) (e : SheafOfModules.unit Z.ringCatSheaf ≅ B) (W : T.Opens) :
    ((Scheme.Modules.pushforwardCongr hab).hom.app B).app W
      (e.hom.app (a⁻¹ᵁW) 1)=e.hom.app (b⁻¹ᵁW) 1 := by
  have hn := congrArg (fun q => q.app W 1)
    ((Scheme.Modules.pushforwardCongr hab).hom.naturality e.hom)
  simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardCongr_hom_app_app,map_one] using hn

/-- The requested ambient generator equality for the EXISTING canonical
pullback frame on the ENTIRE inverse image. Every local section remains
on its original open throughout the five-factor mate calculation. -/
lemma generator {Z T : Scheme.{u}} (a : Z ⟶ T) (B : T.Modules) (W : T.Opens)
    (e : SheafOfModules.unit W.toScheme.ringCatSheaf ≅ B.restrict W.ι) :
    OpenLineFrameCoordinates318.frame ((Scheme.Modules.pullback a).obj B) (a⁻¹ᵁW)
      (LinePullbackFrames318.frame a B W e) (a⁻¹ᵁW) le_rfl 1=
    LocalPullbackUnit318.pull a B W (OpenLineFrameCoordinates318.frame B W e W le_rfl 1) := by
  let V := a⁻¹ᵁW
  let C := (Scheme.Modules.pullback a).obj B
  let g := LinePullbackFrames318.chartMap a W
  let h := LinePullbackFrames318.square a W
  let D := (Scheme.Modules.pullback g).obj (B.restrict W.ι)
  let t := PullbackAdjointUnitFrame318.frame g (B.restrict W.ι) e
  let c := PullbackLineFrames318.chartIso a W.ι V.ι g h B
  let E := LinePullbackFrames318.frame a B W e
  have he : E.hom ≫ c.hom=t.hom := by
    simp only [E,t,c,LinePullbackFrames318.frame,PullbackLineFrames318.frame,
      PullbackAdjointUnitFrame318.frame,Iso.symm_hom,Iso.trans_inv,Functor.mapIso_inv,
      Iso.symm_inv,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hg : t.hom.app (g⁻¹ᵁ(W.ι⁻¹ᵁW)) 1=
      LocalPullbackUnit318.pull g (B.restrict W.ι) (W.ι⁻¹ᵁW)
        (e.hom.app (W.ι⁻¹ᵁW) 1) := by
    have hh := PullbackAdjointUnitFrame318.generator_image g (B.restrict W.ι) D e
      (𝟙 D) (W.ι⁻¹ᵁW)
    simpa only [Scheme.Modules.Hom.id_app,Adjunction.homEquiv_unit,
      Functor.map_id,Category.comp_id] using hh
  have hl := chart_local_unit a W.ι V.ι g h B W
    (OpenLineFrameCoordinates318.frame B W e W le_rfl 1)
  rw [ambient_generator] at hl
  have ht := congr_generator h D t W
  have hs : C.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op
      (OpenLineFrameCoordinates318.frame C V E V le_rfl 1)=
      C.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op
        (LocalPullbackUnit318.pull a B W
          (OpenLineFrameCoordinates318.frame B W e W le_rfl 1)) := by
    apply (ConcreteCategory.bijective_of_isIso (c.hom.app (V.ι⁻¹ᵁV))).1
    apply (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pushforwardCongr h).hom.app D).app W)).1
    rw [ambient_generator]
    have hc := congrArg (fun q => q.app (V.ι⁻¹ᵁV) 1) he
    change c.hom.app (V.ι⁻¹ᵁV) (E.hom.app (V.ι⁻¹ᵁV) 1)=
      t.hom.app (V.ι⁻¹ᵁV) 1 at hc
    rw [hc,ht,hg]
    exact hl.symm
  have hv : V.ι ''ᵁ(V.ι⁻¹ᵁV)=V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,inf_self]
  have hr := congrArg (C.presheaf.map (homOfLE hv.symm.le).op) hs
  simpa only [←C.presheaf.map_comp_apply,←op_comp,homOfLE_comp,
    homOfLE_refl,op_id,Functor.map_id] using hr
end LocalPullbackFrameGenerator318
