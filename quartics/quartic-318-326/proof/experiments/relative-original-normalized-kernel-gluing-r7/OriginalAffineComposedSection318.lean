module
public import OriginalAffineFrameSum318
public section
noncomputable section
namespace OriginalAffineComposedSection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
  (hp : Spec.map g ≫ Spec.map f = Spec.map h)
  (L : Line (Spec A)) (N : Line (Spec C))
  (e : (Scheme.Modules.pullback (Spec.map h)).obj L.object ≅ N.object)
abbrev intermediate := LineSheafPullback318.line (Spec.map f) L

@[expose] def comparison : (Scheme.Modules.pullback (Spec.map g)).obj
    (intermediate A B f L).object ≅ N.object :=
  (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app L.object ≪≫
    (Scheme.Modules.pullbackCongr hp).app L.object ≪≫ e

lemma unit (m : OriginalLineAffineModel318.sections A L) :
    OriginalAffineLinePathSections318.restriction g (intermediate A B f L) N
      (comparison A B C f g h hp L N e)
      (OriginalAffineLinePathSections318.restriction f L (intermediate A B f L) (Iso.refl _) m) =
    OriginalAffineLinePathSections318.restriction h L N e m := by
  simp only [OriginalAffinePathWholeSections318.restriction_direct]
  change e.hom.app ⊤
    (((PullbackPathComposition318.iso (Spec.map g) (Spec.map f) (Spec.map h) hp).hom.app L.object).app ⊤
      (pull (Spec.map g) ((Scheme.Modules.pullback (Spec.map f)).obj L.object)
        (pull (Spec.map f) L.object m))) = e.hom.app ⊤ (pull (Spec.map h) L.object m)
  rw [OriginalSectionPullbackComposition318.path]

@[expose] def restriction : OriginalLineAffineModel318.sections B (intermediate A B f L) →+
    OriginalLineAffineModel318.sections C N where
  toFun := OriginalAffineLinePathSections318.restriction g (intermediate A B f L) N
    (comparison A B C f g h hp L N e)
  map_zero' := by rw [← OriginalAffineLinePathSections318.unit_apply]; simp only [map_zero]
  map_add' := OriginalAffineLinePathSections318.restriction_add _ _ _ _

lemma finite_sum {ι : Type*} [Fintype ι] (a : ι → B)
    (m : ι → OriginalLineAffineModel318.sections A L) :
    restriction A B C f g h hp L N e
      (∑ j, a j • OriginalAffineLinePathSections318.restriction f L (intermediate A B f L) (Iso.refl _) (m j)) =
    ∑ j, g.hom (a j) • OriginalAffineLinePathSections318.restriction h L N e (m j) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change OriginalAffineLinePathSections318.restriction g _ _ _ (_ • _) = _
  rw [OriginalAffineLinePathSections318.restriction_smul,unit]
end OriginalAffineComposedSection318
