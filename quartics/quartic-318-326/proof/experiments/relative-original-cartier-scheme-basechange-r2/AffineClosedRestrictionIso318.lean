module
public import AffineClosedRestriction318
public section
noncomputable section
namespace AffineClosedRestrictionIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z W X : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ X)
  [IsClosedImmersion p] [IsClosedImmersion q] (e : Z ≅ W) (he : e.hom ≫ q=p)
  (A : CommRingCat.{u}) (j : Spec A ⟶ X)
/-- Choice-independent restriction ideal for isomorphic actual closed
source models. Both comparisons preserve the original affine embedding. -/
lemma ideal_eq : AffineClosedRestriction318.ideal p A j=AffineClosedRestriction318.ideal q A j := by
  have h : IsPullback (pullback.fst p j ≫ e.hom) (pullback.snd p j) q j := by
    apply (IsPullback.of_hasPullback p j).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom,Category.id_comp]
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    · simpa only [Iso.refl_hom,Category.comp_id] using he.symm
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  apply AffineClosedQuotientExtraction318.ideal_unique A (pullback.snd p j)
    (AffineClosedRestriction318.ideal q A j)
    (h.isoPullback ≪≫ AffineClosedRestriction318.comparison q A j)
  change (h.isoPullback.hom ≫ (AffineClosedRestriction318.comparison q A j).hom) ≫ _=_
  rw [Category.assoc,AffineClosedQuotientExtraction318.comparison_into,h.isoPullback_hom_snd]
end AffineClosedRestrictionIso318
