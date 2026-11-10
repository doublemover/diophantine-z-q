module
public import PullbackPathComposition318
public section
noncomputable section
namespace OriginalPullbackSquarePasting318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B C D : Scheme.{u}}

/-- Normalize a commuting square through one literal composite path. -/
@[expose] def comparison (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (h : f ≫ g = f' ≫ g') :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback f' :=
  PullbackPathComposition318.iso f g (f' ≫ g') h ≪≫
    (PullbackPathComposition318.iso f' g' (f' ≫ g') rfl).symm

lemma congr_first {f f' : A ⟶ B} (h : f = f') (g : B ⟶ D) (t : A ⟶ D)
    (hf : f ≫ g = t) (hf' : f' ≫ g = t) (M : D.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback g).obj M) ≫
      (PullbackPathComposition318.iso f' g t hf').hom.app M =
        (PullbackPathComposition318.iso f g t hf).hom.app M := by
  subst f'
  simp only [Scheme.Modules.pullbackCongr,eqToIso_refl,NatTrans.id_app,Category.id_comp]

variable {X Y U V U' V' : Scheme.{u}}
  (p : Y ⟶ X) (i : U ⟶ X) (j : V ⟶ X) (e : V ⟶ U) (h : e ≫ i = j)
  (i' : U' ⟶ Y) (j' : V' ⟶ Y) (e' : V' ⟶ U') (h' : e' ≫ i' = j')
  (a : U' ⟶ U) (b : V' ⟶ V)
  (ha : a ≫ i = i' ≫ p) (hb : b ≫ j = j' ≫ p) (he : b ≫ e = e' ≫ a)

/-- Paste actual coefficient-change squares with actual chart-restriction
paths. The comparison is determined by pullback associativity; no
commutation of line-section maps is postulated. -/
lemma paste (M : X.Modules) :
    (Scheme.Modules.pullback b).map ((PullbackPathComposition318.iso e i j h).hom.app M) ≫
      (comparison b j j' p hb).hom.app M =
    (comparison b e e' a he).hom.app ((Scheme.Modules.pullback i).obj M) ≫
      (Scheme.Modules.pullback e').map ((comparison a i i' p ha).hom.app M) ≫
      (PullbackPathComposition318.iso e' i' j' h').hom.app
        ((Scheme.Modules.pullback p).obj M) := by
  have hl : (b ≫ e) ≫ i = j' ≫ p := by rw [Category.assoc,h,hb]
  have hr : (e' ≫ a) ≫ i = j' ≫ p := by rw [Category.assoc,ha,← Category.assoc,h']
  have hm : e' ≫ (i' ≫ p) = j' ≫ p := by rw [← Category.assoc,h']
  let A1 := (PullbackPathComposition318.iso b e (b ≫ e) rfl).hom.app
    ((Scheme.Modules.pullback i).obj M)
  let A2 := (PullbackPathComposition318.iso (b ≫ e) i (j' ≫ p) hl).hom.app M
  let B0 := (Scheme.Modules.pullbackCongr he).hom.app ((Scheme.Modules.pullback i).obj M)
  let A2' := (PullbackPathComposition318.iso (e' ≫ a) i (j' ≫ p) hr).hom.app M
  let A3 := (PullbackPathComposition318.iso e' a (e' ≫ a) rfl).app
    ((Scheme.Modules.pullback i).obj M)
  let A4 := (PullbackPathComposition318.iso a i (i' ≫ p) ha).hom.app M
  let A5 := (PullbackPathComposition318.iso e' (i' ≫ p) (j' ≫ p) hm).hom.app M
  let A6 := (PullbackPathComposition318.iso e' i' j' h').hom.app
    ((Scheme.Modules.pullback p).obj M)
  let A7 := (PullbackPathComposition318.iso j' p (j' ≫ p) rfl).app M
  let A8 := (PullbackPathComposition318.iso i' p (i' ≫ p) rfl).app M
  have H1 : A1 ≫ A2 =
      (Scheme.Modules.pullback b).map ((PullbackPathComposition318.iso e i j h).hom.app M) ≫
        (PullbackPathComposition318.iso b j (j' ≫ p) hb).hom.app M :=
    PullbackPathComposition318.assoc b e i (b ≫ e) j (j' ≫ p) rfl h hl hb M
  have H2 : A3.hom ≫ A2' = (Scheme.Modules.pullback e').map A4 ≫ A5 :=
    PullbackPathComposition318.assoc e' a i (e' ≫ a) (i' ≫ p) (j' ≫ p) rfl ha hr hm M
  have H3 : A6 ≫ A7.hom = (Scheme.Modules.pullback e').map A8.hom ≫ A5 :=
    PullbackPathComposition318.assoc e' i' p j' (i' ≫ p) (j' ≫ p) h' rfl rfl hm M
  have H4 : A2 = B0 ≫ A2' := (congr_first he i (j' ≫ p) hl hr M).symm
  have H5 : A5 ≫ A7.inv = (Scheme.Modules.pullback e').map A8.inv ≫ A6 := by
    apply (cancel_epi ((Scheme.Modules.pullback e').map A8.hom)).mp
    calc
      _ = (A6 ≫ A7.hom) ≫ A7.inv := by rw [← Category.assoc,← H3]
      _ = A6 := by simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
      _ = _ := by simp only [← Functor.map_comp_assoc,Iso.hom_inv_id,
        Functor.map_id,Category.id_comp]
  calc
    _ = A1 ≫ A2 ≫ A7.inv := by
      change _ ≫ ((PullbackPathComposition318.iso b j (j' ≫ p) hb).hom.app M ≫ A7.inv) = _
      rw [← Category.assoc,← H1,Category.assoc]
    _ = A1 ≫ B0 ≫ A2' ≫ A7.inv := by rw [H4,Category.assoc]
    _ = A1 ≫ B0 ≫ A3.inv ≫ (A3.hom ≫ A2') ≫ A7.inv := by
      simp only [Category.assoc,Iso.inv_hom_id_assoc]
    _ = A1 ≫ B0 ≫ A3.inv ≫ (Scheme.Modules.pullback e').map A4 ≫ A5 ≫ A7.inv := by
      rw [H2]; simp only [Category.assoc]
    _ = A1 ≫ B0 ≫ A3.inv ≫ (Scheme.Modules.pullback e').map A4 ≫
        (Scheme.Modules.pullback e').map A8.inv ≫ A6 := by rw [H5]
    _ = _ := by
      simp only [comparison,PullbackPathComposition318.iso,Iso.trans_hom,Iso.symm_hom,
        NatTrans.comp_app,Functor.map_comp,Category.assoc,
        A1,B0,A3,A4,A6,A8,Scheme.Modules.pullbackCongr,eqToIso_refl,
        NatTrans.id_app,Category.comp_id,Category.id_comp]
end OriginalPullbackSquarePasting318
