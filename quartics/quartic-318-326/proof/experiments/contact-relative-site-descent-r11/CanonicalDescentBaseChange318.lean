module
public import CanonicalBaseChangeEndpoint318
public section
noncomputable section
namespace CanonicalDescentBaseChange318
open AlgebraicGeometry CategoryTheory
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B B' U U' : Scheme.{u}} (f : U ⟶ B) (g : U' ⟶ B')
  (a : U' ⟶ U) (b : B' ⟶ B) (square : a ≫ f = g ≫ b) (M : B.Modules)

lemma double_base : doubleMap f g a b square ≫ (first f ≫ f) = (first g ≫ g) ≫ b := by
  rw [← Category.assoc, double_first, Category.assoc, square, ← Category.assoc]

/-- The canonical covering-object comparison preserves the exact original
canonical overlap after base change. No compatibility of this comparison
is an input; both endpoint equations are proved from original paths. -/
lemma overlap_square :
    SheafArrowBaseChange318.overlap a (doubleMap f g a b square)
        ((Scheme.Modules.pullback f).obj M) (first f) (second f) (first g) (second g)
        (double_first f g a b square) (double_second f g a b square)
        (CanonicalSheafOverlap318.actual M f) ≫
      (Scheme.Modules.pullback (second g)).map ((coverComparison f g a b square).hom.app M) =
    (Scheme.Modules.pullback (first g)).map ((coverComparison f g a b square).hom.app M) ≫
      CanonicalSheafOverlap318.actual ((Scheme.Modules.pullback b).obj M) g := by
  let d := doubleMap f g a b square
  let c := first f ≫ f
  let c' := first g ≫ g
  let t := (PullbackPathComposition318.iso d c (c' ≫ b) (double_base f g a b square)).app M
  let t' := (PullbackPathComposition318.iso c' b (c' ≫ b) rfl).app M
  let e₀ := (SheafArrowBaseChange318.endpoint a d (first f) (first g)
    (double_first f g a b square)).app ((Scheme.Modules.pullback f).obj M)
  let e₁ := (SheafArrowBaseChange318.endpoint a d (second f) (second g)
    (double_second f g a b square)).app ((Scheme.Modules.pullback f).obj M)
  let p₀ := (PullbackPathComposition318.iso (first f) f c rfl).app M
  let p₁ := (PullbackPathComposition318.iso (second f) f c (edge_condition f).symm).app M
  let q₀ := (PullbackPathComposition318.iso (first g) g c' rfl).app ((Scheme.Modules.pullback b).obj M)
  let q₁ := (PullbackPathComposition318.iso (second g) g c' (edge_condition g).symm).app
    ((Scheme.Modules.pullback b).obj M)
  let k₀ := (Scheme.Modules.pullback (first g)).mapIso ((coverComparison f g a b square).app M)
  let k₁ := (Scheme.Modules.pullback (second g)).mapIso ((coverComparison f g a b square).app M)
  have h₀ : e₀ ≪≫ (Scheme.Modules.pullback d).mapIso p₀ ≪≫ t = k₀ ≪≫ q₀ ≪≫ t' := by
    apply Iso.ext
    exact CanonicalBaseChangeEndpoint318.to_common f g a b square d (first f) (first g)
      (double_first f g a b square) c c' rfl rfl (double_base f g a b square) M
  have h₁ : e₁ ≪≫ (Scheme.Modules.pullback d).mapIso p₁ ≪≫ t = k₁ ≪≫ q₁ ≪≫ t' := by
    apply Iso.ext
    exact CanonicalBaseChangeEndpoint318.to_common f g a b square d (second f) (second g)
      (double_second f g a b square) c c' (edge_condition f).symm (edge_condition g).symm
      (double_base f g a b square) M
  have hn :
      (e₀ ≪≫ (Scheme.Modules.pullback d).mapIso p₀ ≪≫ t).hom ≫
        (e₁ ≪≫ (Scheme.Modules.pullback d).mapIso p₁ ≪≫ t).inv ≫ k₁.hom =
      k₀.hom ≫ q₀.hom ≫ q₁.inv := by
    rw [h₀, h₁]
    simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  simpa only [e₀, e₁, p₀, p₁, q₀, q₁, k₀, k₁, t, t', c, c', d,
    SheafArrowBaseChange318.overlap, CanonicalSheafOverlap318.actual, CanonicalSheafOverlap318.overlap,
    Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
    using hn
end CanonicalDescentBaseChange318
