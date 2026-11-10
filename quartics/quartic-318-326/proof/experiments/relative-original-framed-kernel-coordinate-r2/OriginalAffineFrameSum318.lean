module
public import OriginalAffineFrameSquare318
public section
noncomputable section
namespace OriginalAffineFrameSum318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B S C : CommRingCat.{u}) (f : A ⟶ B) (i : A ⟶ S)
  (g : S ⟶ C) (k : B ⟶ C)
  (h : Spec.map g ≫ Spec.map i = Spec.map k ≫ Spec.map f)
  (L : Line (Spec A)) (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra B C := k.hom.toAlgebra

@[expose] def coordinate :
    OriginalLineAffineModel318.sections S (OriginalAffineFrameSquare318.sourceLine A S i L) →+ C where
  toFun s := OriginalAffineExtendedFrame318.frame B C k N v
    (OriginalAffineLinePathSections318.restriction g _ _
      (OriginalAffineFrameSquare318.comparison A B S C f i g k h L N e) s)
  map_zero' := by
    rw [← OriginalAffineLinePathSections318.unit_apply]
    simp only [map_zero]
  map_add' s t := by rw [OriginalAffineLinePathSections318.restriction_add,map_add]

lemma coordinate_smul (a : S)
    (s : OriginalLineAffineModel318.sections S (OriginalAffineFrameSquare318.sourceLine A S i L)) :
    coordinate A B S C f i g k h L N e v (a • s) =
      g.hom a * coordinate A B S C f i g k h L N e v s := by
  change OriginalAffineExtendedFrame318.frame B C k N v
    (OriginalAffineLinePathSections318.restriction g _ _ _ (a • s)) = _
  rw [OriginalAffineLinePathSections318.restriction_smul,map_smul]
  rfl

/-- Actual geometric local coordinate of a finite original section sum,
with BOTH ring arrows and original path comparison retained. -/
lemma sum_formula {ι : Type*} [Fintype ι] (a : ι → S)
    (m : ι → OriginalLineAffineModel318.sections A L) :
    coordinate A B S C f i g k h L N e v
      (∑ j, a j • OriginalAffineLinePathSections318.restriction i L
        (OriginalAffineFrameSquare318.sourceLine A S i L) (Iso.refl _) (m j)) =
    ∑ j, g.hom (a j) * k.hom (v (OriginalAffineLinePathSections318.restriction f L N e (m j))) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coordinate_smul]
  congr 1
  exact OriginalAffineFrameSquare318.frame_square A B S C f i g k h L N e v (m j)
end OriginalAffineFrameSum318
