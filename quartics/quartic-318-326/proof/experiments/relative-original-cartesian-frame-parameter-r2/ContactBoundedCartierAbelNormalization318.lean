module
public import OriginalRelativeAbelNormalization318
public section
noncomputable section
namespace ContactBoundedCartierAbelNormalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedCartierEquiv318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "L" => ContactBoundedCartierAbel318.divisorLine c N b D
/-- Actual bounded original Cartier families descend through the
relative quotient by BASE lines, with no choice of a base trivialization. -/
lemma base_twist (M : Line B) : OriginalLineAbelTransformation318.transformation p b
    (OriginalRelativeAbelNormalization318.twist p b L M)=ContactBoundedCartierAbel318.transformation c N b D :=
  OriginalRelativeAbelNormalization318.transformation_twist p b L M
/-- Every all-scheme Abel test is the actual sheaf restriction of the
original full-kernel divisor class, retaining the specified source family. -/
lemma apply_restriction (T : Over (Spec (CommRingCat.of ℚ))) (a : T ⟶ Over.mk b) :
    (ContactBoundedCartierAbel318.transformation c N b D).app (op T) a=
      (RelativeFppfLineSheaf318.sheaf p).obj.map a.op
        (RelativeClassSheafPoint318.value p b (OriginalLineAbelTransformation318.point p b L)) :=
  OriginalAbelSheafValue318.apply_restriction p b L T a
/-- The parameter-fiber construction gives the same original sheaf
value, not a separately chosen Abel map. -/
lemma fiber_value (T : Over (Spec (CommRingCat.of ℚ))) (a : T ⟶ Over.mk b) :
    (ContactBoundedCartierAbel318.fiberTransformation c N b
      (ContactBoundedCartierEquiv318.equivalence c N b D)).app (op T) a=
      (ContactBoundedCartierAbel318.transformation c N b D).app (op T) a := by
  rw [← ContactBoundedCartierAbel318.classification]
end ContactBoundedCartierAbelNormalization318
