module
public import RelativeClassSheafPoint318
public section
noncomputable section
namespace OriginalAbelSheafValue318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable {C S B : Scheme.{0}} (p : C ⟶ S) (b : B ⟶ S)
  (L : Line (pullback p b))
local notation "F" => RelativeFppfLineSheaf318.sheaf p

/-- The actual Abel transformation is obtained by restricting its SAME
associated-sheaf value along every original scheme test map. -/
lemma apply_restriction (T : Over S) (a : T ⟶ Over.mk b) :
    (OriginalLineAbelTransformation318.transformation p b L).app (op T) a=
      F.obj.map a.op (RelativeClassSheafPoint318.value p b
        (OriginalLineAbelTransformation318.point p b L)) := by
  change RelativeClassSheafPoint318.value p T.hom
    (RelativeLineClassBaseChange318.testMap p b T.hom a.left a.w
      (OriginalLineAbelTransformation318.point p b L))=_
  exact (RelativeClassSheafPoint318.value_restrict p b T.hom a.left a.w
    (OriginalLineAbelTransformation318.point p b L)).symm

/-- Equality AFTER actual sheafification suffices to identify Abel maps
on ALL schemes, even when a base-line twist prevents global absolute
line-class equality. -/
lemma value_congr (N : Line (pullback p b))
    (h : RelativeClassSheafPoint318.value p b (OriginalLineAbelTransformation318.point p b L)=
      RelativeClassSheafPoint318.value p b (OriginalLineAbelTransformation318.point p b N)) :
    OriginalLineAbelTransformation318.transformation p b L=
      OriginalLineAbelTransformation318.transformation p b N := by
  ext T a
  rw [apply_restriction,apply_restriction,h]
end OriginalAbelSheafValue318
