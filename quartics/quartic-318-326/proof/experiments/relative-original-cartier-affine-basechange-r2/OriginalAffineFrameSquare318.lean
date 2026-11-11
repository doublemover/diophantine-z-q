module
public import OriginalAffineExtendedFrame318
public import OriginalCoefficientGlobalUnit318
public section
noncomputable section
namespace OriginalAffineFrameSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (A B S C : CommRingCat.{u}) (f : A ⟶ B) (i : A ⟶ S)
  (g : S ⟶ C) (k : B ⟶ C)
  (h : Spec.map g ≫ Spec.map i = Spec.map k ≫ Spec.map f)
  (L : Line (Spec A)) (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra B C := k.hom.toAlgebra
abbrev sourceLine := LineSheafPullback318.line (Spec.map i) L
abbrev targetLine := LineSheafPullback318.line (Spec.map k) N

/-- Actual comparison around the original affine square, then genuine
pullback of the specified original local frame path. -/
@[expose] def comparison :
    (Scheme.Modules.pullback (Spec.map g)).obj (sourceLine A S i L).object ≅
      (targetLine B C k N).object :=
  (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map i)).app L.object ≪≫
    (Scheme.Modules.pullbackCongr h).app L.object ≪≫
    ((Scheme.Modules.pullbackComp (Spec.map k) (Spec.map f)).app L.object).symm ≪≫
    (Scheme.Modules.pullback (Spec.map k)).mapIso e

/-- The exact original affine pullback path carries a section obtained
from the original line around the square to the unchanged opposite path. -/
lemma section_square (m : OriginalLineAffineModel318.sections A L) :
    OriginalAffineLinePathSections318.restriction g (sourceLine A S i L) (targetLine B C k N)
      (comparison A B S C f i g k h L N e)
      (OriginalAffineLinePathSections318.restriction i L (sourceLine A S i L) (Iso.refl _) m) =
    OriginalAffineLinePathSections318.restriction k N (targetLine B C k N) (Iso.refl _)
      (OriginalAffineLinePathSections318.restriction f L N e m) := by
  simp only [OriginalAffinePathWholeSections318.restriction_direct]
  change (((Scheme.Modules.pullback (Spec.map k)).map e.hom).app ⊤)
    (((Scheme.Modules.pullbackComp (Spec.map g) (Spec.map i)).app L.object ≪≫
      (Scheme.Modules.pullbackCongr h).app L.object ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map k) (Spec.map f)).app L.object).symm).hom.app ⊤
        (pull (Spec.map g) ((Scheme.Modules.pullback (Spec.map i)).obj L.object)
          (pull (Spec.map i) L.object m))) =
    pull (Spec.map k) N.object (e.hom.app ⊤ (pull (Spec.map f) L.object m))
  rw [OriginalSectionPullbackComposition318.square]
  exact OriginalSectionPullbackComposition318.naturality (Spec.map k) e.hom _

/-- At the use site, the transported ACTUAL frame sees exactly the
original local coordinate under the actual target ring map. -/
lemma frame_square (m : OriginalLineAffineModel318.sections A L) :
    OriginalAffineExtendedFrame318.frame B C k N v
      (OriginalAffineLinePathSections318.restriction g (sourceLine A S i L) (targetLine B C k N)
        (comparison A B S C f i g k h L N e)
        (OriginalAffineLinePathSections318.restriction i L (sourceLine A S i L) (Iso.refl _) m)) =
      k.hom (v (OriginalAffineLinePathSections318.restriction f L N e m)) := by
  rw [section_square,OriginalAffineExtendedFrame318.frame_unit]
end OriginalAffineFrameSquare318
