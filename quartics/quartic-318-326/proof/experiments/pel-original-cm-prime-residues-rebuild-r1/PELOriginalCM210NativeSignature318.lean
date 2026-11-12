module
public import PELOriginalCM210NativeDiscriminant318
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public section
noncomputable section
namespace PELOriginalCM210NativeSignature318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeDiscriminant318
open NumberField.InfinitePlace
lemma degree_two : Module.finrank ℚ K=2 := QuadraticAlgebra.finrank_eq_two
lemma complex_places : nrComplexPlaces K=1 := by
  have hdeg := card_add_two_mul_card_eq_rank K
  rw [degree_two] at hdeg
  have hcases : nrComplexPlaces K=0 ∨ nrComplexPlaces K=1 := by omega
  rcases hcases with h|h
  · have hs := NumberField.sign_discr K
    rw [native_discriminant,h] at hs
    norm_num at hs
  · exact h
lemma real_places : nrRealPlaces K=0 := by
  have hdeg := card_add_two_mul_card_eq_rank K
  rw [degree_two,complex_places] at hdeg
  omega

end PELOriginalCM210NativeSignature318
