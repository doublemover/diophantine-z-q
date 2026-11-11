module
public import AffineClosedRestriction318
public import AffineQuotientKernelSections318
public section
noncomputable section
namespace AffineClosedRestrictionChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (A : CommRingCat.{u}) (j : Spec A ⟶ X)
local notation "I" => AffineClosedRestriction318.ideal p A j
@[expose] def into : Spec (CommRingCat.of (A ⧸ I)) ⟶ Z :=
  (AffineClosedRestriction318.comparison p A j).inv ≫ pullback.fst p j
/-- The complete extracted affine ideal has its actual quotient chart
in the original closed subscheme, before any regularity assumption. -/
lemma cartesian : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (into p A j) j p := by
  apply (IsPullback.of_hasPullback p j).flip.of_iso
    (AffineClosedRestriction318.comparison p A j) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom,Category.comp_id] using
      (AffineClosedQuotientExtraction318.comparison_into A (pullback.snd p j)).symm
  · simp only [into,Iso.refl_hom,Category.comp_id,Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
lemma kernel [IsOpenImmersion j] :
    (p.ker.ideal (AffineQuotientKernelSections318.chartOpen A j)).comap
      (AffineQuotientKernelSections318.coefficient A j).hom=I :=
  AffineQuotientKernelSections318.original_kernel A I p j (into p A j) (cartesian p A j)
end AffineClosedRestrictionChart318
