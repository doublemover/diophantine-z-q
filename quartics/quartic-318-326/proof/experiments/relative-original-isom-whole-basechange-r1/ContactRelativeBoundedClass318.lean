module
public import ContactNormalizedRelativeBounded318
public section
noncomputable section
namespace ContactRelativeBoundedClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (N : ℕ)
  {B T : Scheme.{0}} (b : B ⟶ Spec R) (t : T ⟶ Spec R) (j : T ⟶ B) (hj : j ≫ b=t)
  (D : ContactBoundedCartierEquiv318.Data c N (b ≫ baseMap R))
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "D'" => ContactBoundedCartierBaseChange318.map c N (b ≫ baseMap R) (t ≫ baseMap R)
  j (by rw [←Category.assoc,hj]) D
lemma relative_class : OriginalLineAbelTransformation318.point q t (ContactRelativeBoundedLine318.line R c N t D')=
    RelativeLineClassBaseChange318.testMap q b t j hj
      (OriginalLineAbelTransformation318.point q b (ContactRelativeBoundedLine318.line R c N b D)) := by
  rw [OriginalLineAbelTransformation318.point,RelativeLineClassBaseChange318.testMap_class]
  rw [ContactRelativeBoundedLine318.coefficient]
  rfl
lemma original_restriction (L : Class (curve R c))
    (h : value q b (OriginalLineAbelTransformation318.point q b (ContactRelativeBoundedLine318.line R c N b D))=
      value q b (original q b L)) :
    value q t (OriginalLineAbelTransformation318.point q t (ContactRelativeBoundedLine318.line R c N t D'))=
      value q t (original q t L) := by
  rw [relative_class]
  exact RelativeOriginalClassRestriction318.restrict_equal q b t j hj L _ h
end ContactRelativeBoundedClass318
