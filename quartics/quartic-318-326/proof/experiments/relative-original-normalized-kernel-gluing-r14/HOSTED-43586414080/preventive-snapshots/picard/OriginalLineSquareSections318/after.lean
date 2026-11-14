module
public import OriginalSectionPullbackComposition318
public import OriginalPullbackSquarePasting318
public section
noncomputable section
namespace OriginalLineSquareSections318
open AlgebraicGeometry CategoryTheory
open OriginalSectionPullbackComposition318 OriginalPullbackSquarePasting318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U V U' V' : Scheme.{u}}
  (p : Y ⟶ X) (i : U ⟶ X) (j : V ⟶ X) (e : V ⟶ U) (h : e ≫ i = j)
  (i' : U' ⟶ Y) (j' : V' ⟶ Y) (e' : V' ⟶ U') (h' : e' ≫ i' = j')
  (a : U' ⟶ U) (b : V' ⟶ V)
  (ha : a ≫ i = i' ≫ p) (hb : b ≫ j = j' ≫ p) (he : b ≫ e = e' ≫ a)

include he in
/-- Both orders of actual chart restriction and coefficient pullback
agree on EVERY old chart section. The proof uses original units and
pullback-associator pasting, not a basis or a hypothesized Cech square. -/
lemma original_square (M : X.Modules) (s : Γ((Scheme.Modules.pullback i).obj M,⊤)) :
    ((comparison b j j' p hb).hom.app M).app ⊤
      (pull b ((Scheme.Modules.pullback j).obj M)
        (((PullbackPathComposition318.iso e i j h).hom.app M).app ⊤
          (pull e ((Scheme.Modules.pullback i).obj M) s))) =
    ((PullbackPathComposition318.iso e' i' j' h').hom.app
      ((Scheme.Modules.pullback p).obj M)).app ⊤
        (pull e' ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback p).obj M))
          (((comparison a i i' p ha).hom.app M).app ⊤
            (pull a ((Scheme.Modules.pullback i).obj M) s))) := by
  let z := pull b ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback i).obj M))
    (pull e ((Scheme.Modules.pullback i).obj M) s)
  have hp := congrArg (fun q => q.app ⊤ z)
    (OriginalPullbackSquarePasting318.paste p i j e h i' j' e' h' a b ha hb he M)
  have hs : ((comparison b e e' a he).hom.app ((Scheme.Modules.pullback i).obj M)).app ⊤ z =
      pull e' ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback i).obj M))
        (pull a ((Scheme.Modules.pullback i).obj M) s) := by
    simpa only [comparison,PullbackPathComposition318.iso,Iso.trans_hom,Iso.symm_hom,
      Iso.trans_inv,Iso.refl_hom,Iso.refl_inv,Iso.app_hom,Iso.app_inv,NatTrans.comp_app,Scheme.Modules.pullbackCongr,eqToIso_refl,NatTrans.id_app,
      Category.comp_id,Category.assoc] using
        OriginalSectionPullbackComposition318.square b e e' a he
          ((Scheme.Modules.pullback i).obj M) s
  calc
    _ = ((comparison b j j' p hb).hom.app M).app ⊤
        (((Scheme.Modules.pullback b).map
          ((PullbackPathComposition318.iso e i j h).hom.app M)).app ⊤ z) := by
      rw [naturality]
    _ = ((PullbackPathComposition318.iso e' i' j' h').hom.app
        ((Scheme.Modules.pullback p).obj M)).app ⊤
          (((Scheme.Modules.pullback e').map ((comparison a i i' p ha).hom.app M)).app ⊤
            (((comparison b e e' a he).hom.app ((Scheme.Modules.pullback i).obj M)).app ⊤ z)) := hp
    _ = _ := by rw [hs,naturality]
end OriginalLineSquareSections318
