module
public import ContactBoundedCartierAbel318
public section
noncomputable section
namespace OriginalRelativeAbelNormalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
universe u
variable {C S B : Scheme.{u}} (p : C ⟶ S) (b : B ⟶ S)
  (L K : Line (pullback p b))
/-- Equality in the ACTUAL relative Picard quotient, not equality of
absolute line classes, determines the entire all-test Abel transformation. -/
lemma relative_congr (h : OriginalLineAbelTransformation318.point p b L=
    OriginalLineAbelTransformation318.point p b K) :
    OriginalLineAbelTransformation318.transformation p b L=
      OriginalLineAbelTransformation318.transformation p b K := by
  ext T a
  change (RelativeFppfLineSheaf318.unit p).app T
    (RelativeLineClassBaseChange318.testMap p b T.unop.hom a.left a.w
      (OriginalLineAbelTransformation318.point p b L))=_
  rw [h]
variable (M : Line B)
@[expose] def twist : Line (pullback p b) :=
  LineSheafTensor318.line L (LineSheafPullback318.line (pullback.snd p b) M)
lemma relative_twist : OriginalLineAbelTransformation318.point p b (twist p b L M)=
    OriginalLineAbelTransformation318.point p b L := by
  change RelativeLineClassQuotient318.classMap (pullback.snd p b)
    (classOf (LineSheafTensor318.line L (LineSheafPullback318.line (pullback.snd p b) M)))=_
  rw [LineSheafClassGroup318.classOf_tensor,map_mul,← LineClassPullbackHom318.on_representatives,
    RelativeLineClassQuotient318.base_class_trivial,mul_one]
/-- Tensoring by any actual base line changes no value of the original
fppf Abel transformation, on ANY scheme test. -/
lemma transformation_twist : OriginalLineAbelTransformation318.transformation p b (twist p b L M)=
    OriginalLineAbelTransformation318.transformation p b L :=
  relative_congr p b _ _ (relative_twist p b L M)
end OriginalRelativeAbelNormalization318
