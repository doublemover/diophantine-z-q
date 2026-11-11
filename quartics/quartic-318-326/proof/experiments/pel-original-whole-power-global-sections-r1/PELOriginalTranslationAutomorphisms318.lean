module
public import PELOriginalIntegerEndomorphismLaws318
public section
noncomputable section
namespace PELOriginalTranslationAutomorphisms318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationTransitions318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Translation by an original point is a genuine regular morphism,
constructed through actual addition and the original point section. -/
@[expose] def translation (q : Base τ) : candidate τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (𝟙 _) (π τ hτ≫candidateComplexPoint τ hτ q)
    (by rw [Category.id_comp,Category.assoc,
      PELOriginalProperComplexCandidate318.candidate_point_over,Category.comp_id])
@[reassoc] lemma over_complex (q : Base τ) : translation τ hτ q≫π τ hτ=π τ hτ := by
  rw [translation,combine_over,Category.id_comp]
lemma original_action (q r : Base τ) :
    candidateComplexPoint τ hτ r≫translation τ hτ q=candidateComplexPoint τ hτ (r+q) := by
  apply combine_action τ hτ _ _ _ _ r q (Category.comp_id _)
  rw [←Category.assoc,PELOriginalProperComplexCandidate318.candidate_point_over,Category.id_comp]

lemma translation_zero : translation τ hτ 0=𝟙 _ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ 0) (Category.id_comp _)
  intro r
  rw [original_action,add_zero,Category.comp_id]
lemma translation_comp (q r : Base τ) :
    translation τ hτ q≫translation τ hτ r=translation τ hτ (q+r) := by
  apply unary_ext τ hτ _ _ (by rw [Category.assoc,over_complex,over_complex])
    (over_complex τ hτ (q+r))
  intro s
  rw [←Category.assoc,original_action,original_action,original_action,add_assoc]

/-- Full scheme automorphism, with its actual inverse and unchanged
complex structure map. The inverse equations hold on all scheme data. -/
@[expose] def translationIso (q : Base τ) : candidate τ hτ ≅ candidate τ hτ where
  hom := translation τ hτ q
  inv := translation τ hτ (-q)
  hom_inv_id := by rw [translation_comp,add_neg_cancel,translation_zero]
  inv_hom_id := by rw [translation_comp,neg_add_cancel,translation_zero]

/-- Genuine compatibility of multiplication and translations. -/
theorem multiplication_translation (n : ℤ) (q : Base τ) :
    translation τ hτ q≫PELOriginalIntegerMultiplication318.multiplication τ hτ n=
      PELOriginalIntegerMultiplication318.multiplication τ hτ n≫translation τ hτ (n • q) := by
  apply unary_ext τ hτ
  · rw [Category.assoc,PELOriginalIntegerMultiplication318.over_complex,over_complex]
  · rw [Category.assoc,over_complex,PELOriginalIntegerMultiplication318.over_complex]
  intro r
  rw [←Category.assoc,original_action,PELOriginalIntegerMultiplication318.original_action,
    ←Category.assoc,PELOriginalIntegerMultiplication318.original_action,original_action,zsmul_add]
end PELOriginalTranslationAutomorphisms318
