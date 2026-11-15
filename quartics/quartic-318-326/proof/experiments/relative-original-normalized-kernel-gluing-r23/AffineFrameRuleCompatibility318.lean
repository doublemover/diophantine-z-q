module
public import AffineFrameOverlapCover318
public section
noncomputable section
namespace AffineFrameRuleCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFrameCoverSections318
universe u
variable {X : Scheme.{u}} (L : Line X) (F : AffineFrameRule318.Rule L) (U : X.AffineOpenCover)
@[expose] def localFrames : LocalFrames L (fun i => Spec (U.X i)) U.f := fun i => F.app (U.X i) (U.f i)
lemma value_on_test (S T : CommRingCat.{u}) (a : Spec T ⟶ Spec S)
    (x : Spec S ⟶ X) (y : Spec T ⟶ X) [IsOpenImmersion a]
    [IsOpenImmersion x] [IsOpenImmersion y] (h : a ≫ x=y) :
    L.object.presheaf.map (homOfLE (show y ''ᵁ ⊤≤x ''ᵁ ⊤ by
      rw [←h]; exact OpenChartSections318.imageLE a x)).op
      (OriginalOpenPullbackSections318.sectionsEquiv x L.object ((F.app S x).hom.app ⊤ 1))=
    OriginalOpenPullbackSections318.sectionsEquiv y L.object ((F.app T y).hom.app ⊤ 1) := by
  have hh := OriginalFrameOpenPath318.value a x y h L (F.app S x)
  rw [F.natural S T a x y h] at hh
  exact hh.symm
/-- Naturality on ALL affine test arrows derives whole-overlap section
compatibility on any actual affine cover. It is not assumed as extra data. -/
lemma compatible : Compatible L (fun i => Spec (U.X i)) U.f (localFrames L F U) := by
  intro i j
  let V := AffineFrameOverlapCover318.cover U i j
  let z := AffineFrameOverlapCover318.into U i j
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.object.presheaf,L.object.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun k => z k ''ᵁ ⊤) ((U.f i ''ᵁ ⊤) ⊓ (U.f j ''ᵁ ⊤))
    (fun k => homOfLE (AffineFrameOverlapCover318.image_le U i j k))
    (AffineFrameOverlapCover318.covers U i j)
  intro k
  rw [←Functor.map_comp_apply,←Functor.map_comp_apply]
  change L.object.presheaf.map _
    (OriginalOpenPullbackSections318.sectionsEquiv (U.f i) L.object ((F.app (U.X i) (U.f i)).hom.app ⊤ 1))=
    L.object.presheaf.map _
    (OriginalOpenPullbackSections318.sectionsEquiv (U.f j) L.object ((F.app (U.X j) (U.f j)).hom.app ⊤ 1))
  exact (value_on_test L F (U.X i) (V.X k) (AffineFrameOverlapCover318.left U i j k)
    (U.f i) (z k) rfl).trans
      (value_on_test L F (U.X j) (V.X k) (AffineFrameOverlapCover318.right U i j k)
        (U.f j) (z k) (AffineFrameOverlapCover318.right_into U i j k)).symm
end AffineFrameRuleCompatibility318
