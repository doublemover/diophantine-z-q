module
public import AffineChangedBaseEffectivity318
public section
noncomputable section
namespace CanonicalBaseChangeEndpoint318
open AlgebraicGeometry CategoryTheory
open ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' V V' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (square : a ≫ f = g ≫ b)
  (d : V' ⟶ V) (p : V ⟶ U) (r : V' ⟶ U') (hdp : d ≫ p = r ≫ a)
  (c : V ⟶ B) (c' : V' ⟶ B') (hp : p ≫ f = c) (hr : r ≫ g = c')
  (hd : d ≫ c = c' ≫ b) (M : B.Modules)

/-- Both routes around the original base-change endpoint rectangle reach
the exact same composite pullback. This is derived from three original
named-path associativity identities, with no new coherence premise. -/
lemma to_common :
    (SheafArrowBaseChange318.endpoint a d p r hdp).hom.app ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pullback d).map ((PullbackPathComposition318.iso p f c hp).hom.app M) ≫
        (PullbackPathComposition318.iso d c (c' ≫ b) hd).hom.app M =
    (Scheme.Modules.pullback r).map ((coverComparison f g a b square).hom.app M) ≫
      (PullbackPathComposition318.iso r g c' hr).hom.app ((Scheme.Modules.pullback b).obj M) ≫
        (PullbackPathComposition318.iso c' b (c' ≫ b) rfl).hom.app M := by
  have hrg : r ≫ (g ≫ b) = c' ≫ b := by rw [← Category.assoc, hr]
  have hraf : (r ≫ a) ≫ f = c' ≫ b := by rw [Category.assoc, square, hrg]
  have hold := PullbackPathComposition318.assoc d p f (r ≫ a) c (c' ≫ b) hdp hp hraf hd M
  have hsquare := PullbackPathComposition318.assoc r a f (r ≫ a) (g ≫ b) (c' ≫ b)
    rfl square hraf hrg M
  have hnew := PullbackPathComposition318.assoc r g b c' (g ≫ b) (c' ≫ b) hr rfl rfl hrg M
  simp only [SheafArrowBaseChange318.endpoint, coverComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← hold, Iso.inv_hom_id_app_assoc, hsquare, hnew]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
end CanonicalBaseChangeEndpoint318
