module
public import SchemeClosedFamilyCoverModels318
public section
noncomputable section
namespace ContactSchemeUniversalRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactSchemeHilbertData318.Data c n b)
local notation "x" => ContactSchemeHilbertEquiv318.equivalence c n b D
abbrev comparison := ContactSchemeHilbertRecovery318.comparison c n b D
@[reassoc] lemma comparison_source : (comparison c n b D).hom ≫ ContactSchemePointFamily318.into c n b x=
    D.ideal.subschemeι := ContactSchemeHilbertRecovery318.comparison_source c n b D
abbrev toFamily : D.ideal.subscheme ⟶ ContactProjectiveUniversalGluing318.family c n :=
  (comparison c n b D).hom ≫ ContactSchemePointFamily318.toFamily c n b x
/-- Every STANDARD arbitrary-base original quotient has an actual source
Cartesian comparison with the global universal family. -/
lemma cartesian : IsPullback (toFamily c n b D) D.ideal.subschemeι
    (ContactProjectiveUniversalGluing318.original c n) (ContactSchemePointFamily318.sourceMap c n b x) := by
  have H := ContactSchemePointFamily318.cartesian c n b x
  apply H.of_iso (comparison c n b D).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [toFamily,Iso.symm_hom,Iso.refl_hom,Category.comp_id,Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom,Iso.refl_hom,Category.comp_id]
    rw [← comparison_source,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
end ContactSchemeUniversalRecovery318
