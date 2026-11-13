module
public import PELOriginalCM210ThirdRadicalField318
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace PELOriginalCM210RadicalTower318
open PELOriginalCM210PrimeDiscriminantData318
abbrev First := PELOriginalCM210FirstTwoRadicalFields318.First
abbrev Second := PELOriginalCM210FirstTwoRadicalFields318.Second
abbrev Third := PELOriginalCM210ThirdRadicalField318.Third
lemma fourth_radicand_nonsquare : ¬IsSquare (algebraMap ℚ Third (-7)) := by
  apply PELOriginalCM210ThirdRadicalField318.third_nonsquare
  · exact negative_not_square 2
  · simpa [positiveClass] using positive_not_square 2
  · simpa [positiveClass] using positive_not_square 3
  · simpa [negativeClass] using negative_not_square 6
  · simpa [negativeClass] using negative_not_square 5
  · simpa [positiveClass] using positive_not_square 5
  · simpa [positiveClass] using positive_not_square 6
  · simpa [negativeClass] using negative_not_square 7
abbrev H := QuadraticAlgebra Third (algebraMap ℚ Third (-7)) 0
@[reducible, expose] instance fourthField : Field H := by
  letI : Fact (¬IsSquare (algebraMap ℚ Third (-7))) := ⟨fourth_radicand_nonsquare⟩
  infer_instance
instance secondFinite : Module.Finite ℚ Second := Module.Finite.trans First Second
instance thirdFinite : Module.Finite ℚ Third := Module.Finite.trans Second Third
instance fourthFinite : Module.Finite ℚ H := Module.Finite.trans Third H
instance : NumberField H where
lemma degree_two : Module.finrank ℚ First=2 := QuadraticAlgebra.finrank_eq_two
lemma degree_four : Module.finrank ℚ Second=4 := by
  rw [←Module.finrank_mul_finrank ℚ First Second,degree_two,QuadraticAlgebra.finrank_eq_two]
lemma degree_eight : Module.finrank ℚ Third=8 := by
  rw [←Module.finrank_mul_finrank ℚ Second Third,degree_four,QuadraticAlgebra.finrank_eq_two]
lemma degree_sixteen : Module.finrank ℚ H=16 := by
  rw [←Module.finrank_mul_finrank ℚ Third H,degree_eight,QuadraticAlgebra.finrank_eq_two]
end PELOriginalCM210RadicalTower318
