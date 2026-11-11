module
public import PELOriginalIntegerMultiplication318
public section
noncomputable section
namespace PELOriginalIntegerEndomorphismLaws318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemeGroupUnitInverse318
open PELOriginalIntegerMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma multiplication_zero : multiplication τ hτ 0=constantZero τ hτ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ 0) (constantZero_over τ hτ)
  intro q
  simpa only [zero_smul,constantZero_action,zeroPoint] using original_action τ hτ 0 q
lemma multiplication_one : multiplication τ hτ 1=𝟙 _ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ 1) (Category.id_comp _)
  intro q
  rw [original_action,one_smul,Category.comp_id]
lemma multiplication_neg_one : multiplication τ hτ (-1)=inverse τ hτ := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ (-1)) (inverse_over τ hτ)
  intro q
  rw [original_action,neg_one_zsmul,inverse_action]

/-- Addition of scalars is the actual pointwise sum of regular maps. -/
theorem multiplication_add (n m : ℤ) :
    multiplication τ hτ (n+m)=combine τ hτ (multiplication τ hτ n) (multiplication τ hτ m)
      ((over_complex τ hτ n).trans (over_complex τ hτ m).symm) := by
  apply unary_ext τ hτ _ _ (over_complex τ hτ (n+m))
    ((combine_over τ hτ _ _ _).trans (over_complex τ hτ n))
  intro q
  rw [original_action,combine_action τ hτ _ _ _ _ (n • q) (m • q)
    (original_action τ hτ n q) (original_action τ hτ m q),add_zsmul]

/-- Actual composition law, with categorical order explicit. -/
theorem multiplication_comp (n m : ℤ) :
    multiplication τ hτ n≫multiplication τ hτ m=multiplication τ hτ (m*n) := by
  apply unary_ext τ hτ _ _ (by rw [Category.assoc,over_complex,over_complex])
    (over_complex τ hτ (m*n))
  intro q
  rw [←Category.assoc,original_action,original_action,original_action,mul_smul]

/-- Multiplication by n is a group ENDOMORPHISM as a full binary scheme
square, not merely a self-map with the right complex-point action. -/
theorem multiplication_addition (n : ℤ) :
    PELOriginalAdditionSchemeMorphism318.addition τ hτ≫multiplication τ hτ n=
      combine τ hτ (pullback.fst (π τ hτ) (π τ hτ)≫multiplication τ hτ n)
        (pullback.snd (π τ hτ) (π τ hτ)≫multiplication τ hτ n)
        (by simp only [Category.assoc,over_complex]; exact pullback.condition) := by
  apply PELOriginalProductComplexPoints318.morphism_ext τ hτ
  · rw [Category.assoc,over_complex]
    exact PELOriginalAdditionSchemeMorphism318.over_complex τ hτ
  · rw [combine_over,Category.assoc,over_complex]
    rfl
  intro z a
  have hf := pair_fst_assoc τ hτ (DiscreteComplexPeriodAtlas318.projection (QuaternionicRealPeriod318.P τ) z)
    (DiscreteComplexPeriodAtlas318.projection (QuaternionicRealPeriod318.P τ) a) (multiplication τ hτ n)
  have hg := pair_snd_assoc τ hτ (DiscreteComplexPeriodAtlas318.projection (QuaternionicRealPeriod318.P τ) z)
    (DiscreteComplexPeriodAtlas318.projection (QuaternionicRealPeriod318.P τ) a) (multiplication τ hτ n)
  rw [original_action] at hf hg
  rw [←Category.assoc,PELOriginalAdditionSchemeMorphism318.pair_action,original_action,
    combine_action τ hτ _ _ _ _ _ _ hf hg,zsmul_add]
end PELOriginalIntegerEndomorphismLaws318
