module
public import ContactNormalizedPairData318
public section
noncomputable section
namespace ContactNormalizedPairClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactNormalizedPairData318 RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (A B : Line (curve R c))
  (hA : ∀ x : NonreducedLineMayerVietoris318.H1 A,x=0)
  (hB : ∀ x : NonreducedLineMayerVietoris318.H1 B,x=0)
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "t" => projection R c A B hA hB
abbrev firstLine := ContactRelativeBoundedLine318.line R c (firstBound R c A hA) t (firstData R c A B hA hB)
abbrev secondLine := ContactRelativeBoundedLine318.line R c (secondBound R c B hB) t (secondData R c A B hA hB)
lemma first_value : value q t (OriginalLineAbelTransformation318.point q t (firstLine R c A B hA hB))=
    value q t (original q t (classOf A)) :=
  ContactRelativeBoundedClass318.original_restriction R c (firstBound R c A hA)
    (firstBase R c A hA) t (first R c A B hA hB) (first_over R c A B hA hB)
    (ContactNormalizedBoundedCartier318.data R c A hA) (classOf A)
    (ContactNormalizedRelativeBounded318.original_value R c A hA)
lemma second_value : value q t (OriginalLineAbelTransformation318.point q t (secondLine R c A B hA hB))=
    value q t (original q t (classOf B)) :=
  ContactRelativeBoundedClass318.original_restriction R c (secondBound R c B hB)
    (secondBase R c B hB) t (second R c A B hA hB) (second_over R c A B hA hB)
    (ContactNormalizedBoundedCartier318.data R c B hB) (classOf B)
    (ContactNormalizedRelativeBounded318.original_value R c B hB)
/-- The ACTUAL difference line of the two bounded classified families. -/
@[expose] def line : Line (pullback q t) :=
  LineSheafTensor318.line (firstLine R c A B hA hB)
    (FramedLineInverse318.inverse (secondLine R c A B hA hB))
lemma relative_class : OriginalLineAbelTransformation318.point q t (line R c A B hA hB)=
    OriginalLineAbelTransformation318.point q t (firstLine R c A B hA hB) *
      (OriginalLineAbelTransformation318.point q t (secondLine R c A B hA hB))⁻¹ := by
  change RelativeLineClassQuotient318.classMap (pullback.snd q t)
    (classOf (LineSheafTensor318.line _ (FramedLineInverse318.inverse _)))=_
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,map_mul,map_inv]
  rfl
/-- The two actual bounded Cartier families represent the original
line difference in the genuine relative fppf sheaf on their WHOLE common
parameter. Absolute line-class equality is not asserted. -/
lemma value_difference : value q t (OriginalLineAbelTransformation318.point q t (line R c A B hA hB))=
    value q t (original q t (classOf A*(classOf B)⁻¹)) := by
  rw [relative_class,map_mul,map_inv,first_value,second_value]
  simp only [original,map_mul,map_inv]
end ContactNormalizedPairClass318
