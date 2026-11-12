module
public import ContactProjectiveAbelMap318
public import ContactSectionDivisorClass318
public section
noncomputable section
namespace ContactSectionAbelRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
  (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s)
local notation "D" => ContactSectionQuotientData318.datum R c L s
local notation "hf" => ContactSectionQuotientCartier318.finite_regular R c L s hs
local notation "hi" => ContactSectionQuotientCartier318.infinity_regular R c L s hs
local notation "p" => ContactOriginalAffineTestCover318.p c
local notation "b" => ContactOriginalRelativePolynomialCharts318.baseMap R
/-- The arbitrary full-ideal projective divisor construction recovers the
original line's Abel transformation on ALL schemes, including nonreduced
tests, by its actual dual kernel and proved whole-line-class identity. -/
lemma transformation_eq : ContactProjectiveAbelMap318.transformation R c D hf hi=
    OriginalLineAbelTransformation318.transformation p b L :=
  OriginalLineAbelTransformation318.class_congr p b
    (ContactSectionDivisorClass318.divisorLine R c L s hs) L
    (ContactSectionDivisorClass318.divisor_class R c L s hs)
lemma value_eq : RelativeClassSheafPoint318.value p b
    (OriginalLineAbelTransformation318.point p b (ContactSectionDivisorClass318.divisorLine R c L s hs))=
    RelativeClassSheafPoint318.value p b (OriginalLineAbelTransformation318.point p b L) := by
  apply congrArg (RelativeClassSheafPoint318.value p b)
  apply congrArg (RelativeLineClassQuotient318.classMap (pullback.snd p b))
  exact ContactSectionDivisorClass318.divisor_class R c L s hs
end ContactSectionAbelRecovery318
