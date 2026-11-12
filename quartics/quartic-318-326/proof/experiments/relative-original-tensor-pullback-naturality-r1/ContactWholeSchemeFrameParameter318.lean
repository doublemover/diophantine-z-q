module
public import ContactAllAffineFrameClassifier318
public section
noncomputable section
namespace ContactWholeSchemeFrameParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (T : Scheme.{0}) (b : T ⟶ Spec R)
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
local notation "q" => ContactAllAffineFrameClassifier318.projection R c L
local notation "E" => ContactAllAffineFrameClassifier318.data R c L
/-- Full original frames on EVERY coefficient scheme are classified by
actual morphisms to the SAME original nowhere-zero open parameter.
This classifies fixed-line frames, not the Picard functor or Jacobian. -/
@[expose] def equivalence :
    {z : T ⟶ ContactAllAffineFrameClassifier318.parameter R c L // z ≫ q=b} ≃
      Frames (LineSheafPullback318.line (pullback.fst p b) L) :=
  WholeFrameClassifierInverse318.equivalence p L q E b
@[expose] def classifyingMap (e : Frames (LineSheafPullback318.line (pullback.fst p b) L)) :
    T ⟶ ContactAllAffineFrameClassifier318.parameter R c L :=
  WholeFrameClassifyingRule318.classify p L q E b e
lemma over (e : Frames (LineSheafPullback318.line (pullback.fst p b) L)) :
    classifyingMap R c L T b e ≫ q=b := WholeFrameClassifyingRule318.over p L q E b e
lemma affine_test (e : Frames (LineSheafPullback318.line (pullback.fst p b) L))
    (S : CommRingCat.{0}) (a : Spec S ⟶ T) :
    a ≫ classifyingMap R c L T b e=
      ((ContactAllAffineFrameClassifier318.equivalence R c L S (a ≫ b)).symm
        (WholeFrameClassifyingRule318.frameAt p L b e S a)).val :=
  WholeFrameClassifyingRule318.test p L q E b e S a
lemma recover_classify (e : Frames (LineSheafPullback318.line (pullback.fst p b) L)) :
    equivalence R c L T b ⟨classifyingMap R c L T b e,over R c L T b e⟩=e :=
  WholeFrameClassifierInverse318.recover_classify p L q E b e
lemma classify_recover (z : {z : T ⟶ ContactAllAffineFrameClassifier318.parameter R c L // z ≫ q=b}) :
    classifyingMap R c L T b (equivalence R c L T b z)=z.val :=
  WholeFrameClassifierInverse318.classify_recover p L q E b z.val z.property
end ContactWholeSchemeFrameParameter318
