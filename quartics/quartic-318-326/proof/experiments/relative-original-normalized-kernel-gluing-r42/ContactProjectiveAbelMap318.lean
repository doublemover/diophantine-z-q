module
public import ContactProjectiveDivisorLine318
public import OriginalAbelSheafValue318
public section
noncomputable section
namespace ContactProjectiveAbelMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
  (hf : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
  (hi : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal)
local notation "p" => ContactOriginalAffineTestCover318.p c
local notation "b" => ContactOriginalRelativePolynomialCharts318.baseMap R
local notation "L" => ContactProjectiveDivisorLine318.line R c D hf hi
/-- The ACTUAL divisor dual of the full glued kernel supplies a natural
Abel transformation on all original scheme tests. The target is the
existing fppf line-class sheaf, not an assumed Jacobian scheme. -/
@[expose] def transformation : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation p b L
lemma apply_restriction (T : Over (Spec (CommRingCat.of ℚ))) (a : T ⟶ Over.mk b) :
    (transformation R c D hf hi).app (op T) a=
      (RelativeFppfLineSheaf318.sheaf p).obj.map a.op
        (RelativeClassSheafPoint318.value p b (OriginalLineAbelTransformation318.point p b L)) :=
  OriginalAbelSheafValue318.apply_restriction p b L T a
lemma frames_independent
    (hf' : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
    (hi' : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal) :
    transformation R c D hf hi=transformation R c D hf' hi' :=
  OriginalLineAbelTransformation318.class_congr p b L
    (ContactProjectiveDivisorLine318.line R c D hf' hi')
    (ContactProjectiveDivisorLine318.frames_independent R c D hf hi hf' hi')
end ContactProjectiveAbelMap318
