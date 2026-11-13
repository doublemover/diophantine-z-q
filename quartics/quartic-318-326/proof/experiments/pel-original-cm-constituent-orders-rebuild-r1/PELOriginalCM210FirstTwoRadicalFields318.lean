module
public import PELOriginalCM210PrimeDiscriminantData318
public section
noncomputable section
namespace PELOriginalCM210FirstTwoRadicalFields318
open PELOriginalCM210PrimeDiscriminantData318
abbrev First := QuadraticAlgebra ℚ (-2) 0
@[reducible, expose] instance firstField : Field First := by
  letI : Fact (¬IsSquare (-2:ℚ)) := ⟨negative_not_square 0⟩
  infer_instance
lemma first_nonsquare (x:ℚ) (hx:¬IsSquare x) (h2:¬IsSquare ((-2)*x)) :
    ¬IsSquare (algebraMap ℚ First x) := by
  intro hs
  rcases (SquareReflection318.quadratic_square_iff (-2:ℚ) x (by norm_num)).mp hs with h|h
  · exact hx h
  · exact h2 h
lemma second_radicand_nonsquare : ¬IsSquare (algebraMap ℚ First (-3)) := by
  apply first_nonsquare
  · exact negative_not_square 1
  · simpa [positiveClass] using positive_not_square 1
abbrev Second := QuadraticAlgebra First (algebraMap ℚ First (-3)) 0
@[reducible, expose] instance secondField : Field Second := by
  letI : Fact (¬IsSquare (algebraMap ℚ First (-3))) := ⟨second_radicand_nonsquare⟩
  infer_instance
lemma second_nonsquare (x:ℚ) (hx:¬IsSquare x) (h2:¬IsSquare ((-2)*x))
    (h3:¬IsSquare ((-3)*x)) (h6:¬IsSquare (6*x)) :
    ¬IsSquare (algebraMap ℚ Second x) := by
  intro hs
  have hs' : IsSquare (algebraMap First Second (algebraMap ℚ First x)) := by
    simpa only [←IsScalarTower.algebraMap_apply] using hs
  rcases (SquareReflection318.quadratic_square_iff (algebraMap ℚ First (-3))
    (algebraMap ℚ First x) (by norm_num)).mp hs' with h|h
  · exact first_nonsquare x hx h2 h
  · have h' : IsSquare (algebraMap ℚ First ((-3)*x)) := by
      simpa only [map_mul] using h
    exact first_nonsquare ((-3)*x) h3
      (by simpa only [show (-2:ℚ)*((-3)*x)=6*x by ring] using h6) h'
end PELOriginalCM210FirstTwoRadicalFields318
