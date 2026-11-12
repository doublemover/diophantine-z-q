module
public import OriginalLineTensorIsoNaturality318
public import PullbackChartComposition318
public section
noncomputable section
namespace OriginalPullbackChartVertical318
open AlgebraicGeometry CategoryTheory PullbackPathComposition318 PullbackChartComposition318
universe u
variable {X Y Z U V W : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z) (j : U ⟶ Z) (k : V ⟶ Y) (l : W ⟶ X)
  (a : V ⟶ U) (b : W ⟶ V) (hk : k ≫ g=a ≫ j) (hl : l ≫ f=b ≫ k)
lemma total : l ≫ (f ≫ g)=(b ≫ a) ≫ j := by
  rw [←Category.assoc,hl,Category.assoc,hk,←Category.assoc]
/-- Vertical composition of the ACTUAL normalized pullback-chart maps,
retaining all native pullback associators and the given literal squares. -/
lemma chart (M : Z.Modules)
    (e : SheafOfModules.unit U.ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M) :
    PullbackChartComposition318.chart f k l b (b ≫ k) hl rfl
      ((Scheme.Modules.pullback g).obj M)
      (PullbackChartComposition318.chart g j k a (a ≫ j) hk rfl M e) ≪≫
      (Scheme.Modules.pullback l).mapIso ((Scheme.Modules.pullbackComp f g).app M)=
    PullbackChartComposition318.chart (f ≫ g) j l (b ≫ a) ((b ≫ a) ≫ j)
      (total f g j k l a b hk hl) rfl M e := by
  have hb : (b ≫ k) ≫ g=(b ≫ a) ≫ j := by
    rw [Category.assoc,hk,←Category.assoc]
  have ht : b ≫ (a ≫ j)=(b ≫ a) ≫ j := (Category.assoc _ _ _).symm
  have hp := PullbackPathComposition318.assoc l f g (b ≫ k) (f ≫ g) ((b ≫ a) ≫ j)
    hl rfl hb (total f g j k l a b hk hl) M
  have hfg : (iso f g (f ≫ g) rfl).hom.app M=
      (Scheme.Modules.pullbackComp f g).hom.app M := by
    simp only [iso,Iso.trans_hom,NatTrans.comp_app,Scheme.Modules.pullbackCongr,
      eqToIso_refl,Iso.refl_hom,NatTrans.id_app,Category.comp_id]
  rw [hfg] at hp
  have hp' : (iso l f (b ≫ k) hl).inv.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pullback l).map ((Scheme.Modules.pullbackComp f g).hom.app M) ≫
      (iso l (f ≫ g) ((b ≫ a) ≫ j) (total f g j k l a b hk hl)).hom.app M=
    (iso (b ≫ k) g ((b ≫ a) ≫ j) hb).hom.app M := by
    have hh := congrArg (fun q =>
      (iso l f (b ≫ k) hl).inv.app ((Scheme.Modules.pullback g).obj M) ≫ q) hp
    simpa only [Category.assoc,Iso.inv_hom_id_app_assoc] using hh.symm
  apply Iso.ext
  apply (cancel_mono
    (iso l (f ≫ g) ((b ≫ a) ≫ j) (total f g j k l a b hk hl)).hom.app M).mp
  have hr := congrArg Iso.hom (PullbackChartComposition318.restrict_chart g j k a
    (a ≫ j) hk rfl b (b ≫ k) (b ≫ a) ((b ≫ a) ≫ j)
    rfl rfl ht hb rfl M e)
  simp only [PullbackChartComposition318.chart,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Category.assoc,Iso.inv_hom_id_app,Category.comp_id] at hr ⊢
  rw [hp']
  exact hr
end OriginalPullbackChartVertical318
