module
public import WholeFrameRecoveryNaturality318
public section
noncomputable section
namespace ContactUniversalFrameClassifier318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
local notation "q" => ContactAllAffineFrameClassifier318.projection R c L
local notation "E" => ContactAllAffineFrameClassifier318.data R c L
@[expose] def universal : Frames (LineSheafPullback318.line (pullback.fst p q) L) :=
  WholeFrameRecoveryNaturality318.universal p L q E
variable (T T' : Scheme.{0}) (b : T ⟶ Spec R) (b' : T' ⟶ Spec R)
  (h : T' ⟶ T) (hh : h ≫ b=b')
/-- Concrete SAME original Contact parameter: whole-scheme classifying
maps commute with every actual coefficient arrow and original frame pullback. -/
lemma classify_natural (e : Frames (LineSheafPullback318.line (pullback.fst p b) L)) :
    ContactWholeSchemeFrameParameter318.classifyingMap R c L T' b'
      (WholeFrameCoefficientNaturality318.pullFrame p L b b' h hh e)=
      h ≫ ContactWholeSchemeFrameParameter318.classifyingMap R c L T b e :=
  WholeFrameCoefficientNaturality318.classify p L q E b b' h hh e
lemma recovery_natural
    (z : {z : T ⟶ ContactAllAffineFrameClassifier318.parameter R c L // z ≫ q=b}) :
    WholeFrameCoefficientNaturality318.pullFrame p L b b' h hh
      (ContactWholeSchemeFrameParameter318.equivalence R c L T b z)=
    ContactWholeSchemeFrameParameter318.equivalence R c L T' b'
      ⟨h ≫ z.val,by rw [Category.assoc,z.property,hh]⟩ :=
  WholeFrameRecoveryNaturality318.recovery p L q E b b' h hh z.val z.property
lemma universal_pullback
    (z : {z : T ⟶ ContactAllAffineFrameClassifier318.parameter R c L // z ≫ q=b}) :
    WholeFrameCoefficientNaturality318.pullFrame p L q b z.val z.property (universal R c L)=
      ContactWholeSchemeFrameParameter318.equivalence R c L T b z :=
  WholeFrameRecoveryNaturality318.universal_pullback p L q E b z.val z.property
end ContactUniversalFrameClassifier318
