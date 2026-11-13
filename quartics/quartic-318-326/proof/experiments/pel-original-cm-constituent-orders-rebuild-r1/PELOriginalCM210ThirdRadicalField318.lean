module
public import PELOriginalCM210FirstTwoRadicalFields318
public section
noncomputable section
namespace PELOriginalCM210ThirdRadicalField318
open PELOriginalCM210PrimeDiscriminantData318 PELOriginalCM210FirstTwoRadicalFields318
lemma third_radicand_nonsquare : ¬IsSquare (algebraMap ℚ Second 5) := by
  apply second_nonsquare
  · exact positive_not_square 0
  · simpa [negativeClass] using negative_not_square 3
  · simpa [negativeClass] using negative_not_square 4
  · simpa [positiveClass] using positive_not_square 4
abbrev Third := QuadraticAlgebra Second (algebraMap ℚ Second 5) 0
@[reducible, expose] instance thirdField : Field Third := by
  letI : Fact (¬IsSquare (algebraMap ℚ Second 5)) := ⟨third_radicand_nonsquare⟩
  infer_instance
lemma third_nonsquare (x:ℚ) (hx:¬IsSquare x) (h2:¬IsSquare ((-2)*x))
    (h3:¬IsSquare ((-3)*x)) (h6:¬IsSquare (6*x))
    (h5:¬IsSquare (5*x)) (h10:¬IsSquare ((-10)*x))
    (h15:¬IsSquare ((-15)*x)) (h30:¬IsSquare (30*x)) :
    ¬IsSquare (algebraMap ℚ Third x) := by
  intro hs
  have hs' : IsSquare (algebraMap Second Third (algebraMap ℚ Second x)) := by
    simpa only [←IsScalarTower.algebraMap_apply] using hs
  rcases (SquareReflection318.quadratic_square_iff (algebraMap ℚ Second 5)
    (algebraMap ℚ Second x) (by norm_num)).mp hs' with h|h
  · exact second_nonsquare x hx h2 h3 h6 h
  · have h' : IsSquare (algebraMap ℚ Second (5*x)) := by
      simpa only [map_mul] using h
    exact second_nonsquare (5*x) h5
      (by simpa only [show (-2:ℚ)*(5*x)=(-10)*x by ring] using h10)
      (by simpa only [show (-3:ℚ)*(5*x)=(-15)*x by ring] using h15)
      (by simpa only [show (6:ℚ)*(5*x)=30*x by ring] using h30) h'
end PELOriginalCM210ThirdRadicalField318
