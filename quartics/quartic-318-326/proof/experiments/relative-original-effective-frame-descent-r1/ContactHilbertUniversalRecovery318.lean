module
public import ContactSchemePointFamily318
public section
noncomputable section
namespace ContactHilbertUniversalRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (D : ContactHilbertData318.FixedRank S c n)
local notation "I" => ContactHilbertIdealCharacterization318.toClassified c n S D
local notation "x" => ContactHilbertFixedRankEquiv318.equivalence c n S D
abbrev comparison : D.val.ideal.subscheme ≅ ContactProjectivePointFamily318.family c n S x :=
  ContactProjectiveInputRecovery318.comparison c n S D.val.ideal.subschemeι
    (ContactProjectiveClassifiedIdeal318.presentation c n S I)
@[reassoc] lemma comparison_source : (comparison c n S D).hom ≫ ContactProjectivePointFamily318.into c n S x=
    D.val.ideal.subschemeι := ContactProjectiveInputRecovery318.comparison_source _ _ _ _ _
abbrev toFamily : D.val.ideal.subscheme ⟶ ContactProjectiveUniversalGluing318.family c n :=
  (comparison c n S D).hom ≫ ContactProjectivePointFamily318.toFamily c n S x
/-- Every STANDARD affine-base original quotient has an actual source
Cartesian comparison with the global universal family. -/
lemma cartesian : IsPullback (toFamily c n S D) D.val.ideal.subschemeι
    (ContactProjectiveUniversalGluing318.original c n) (ContactProjectivePointFamily318.sourceMap c n S x) := by
  have H := ContactProjectivePointFamily318.cartesian c n S x
  apply H.of_iso (comparison c n S D).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [toFamily,Iso.symm_hom,Iso.refl_hom,Category.comp_id,Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom,Iso.refl_hom,Category.comp_id]
    rw [← comparison_source,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
end ContactHilbertUniversalRecovery318
