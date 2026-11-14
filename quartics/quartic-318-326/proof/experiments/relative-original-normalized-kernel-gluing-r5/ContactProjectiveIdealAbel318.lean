module
public import ContactProjectiveCanonicalCartier318
public import ContactProjectiveAbelMap318
public section
noncomputable section
namespace ContactProjectiveIdealAbel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (I : (ContactOriginalRelativePolynomialCharts318.curve R c).IdealSheafData)
  (h : OriginalRegularClosedCharts318.Property I.subschemeι)
local notation "p" => ContactOriginalAffineTestCover318.p c
local notation "b" => ContactOriginalRelativePolynomialCharts318.baseMap R
/-- Intrinsic O(D) from the canonical ideal-sheaf subscheme and its
ACTUAL invertible kernel, with no chart-presentation choice in its class. -/
@[expose] def divisorLine := FramedLineInverse318.inverse (ActualCartierIdealLine318.line I.subschemeι h)
@[expose] def transformation : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation p b (divisorLine R c I h)
lemma regularity_independent (h' : OriginalRegularClosedCharts318.Property I.subschemeι) :
    transformation R c I h=transformation R c I h' := by
  apply OriginalLineAbelTransformation318.class_congr
  change classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line I.subschemeι h))=
    classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line I.subschemeι h'))
  rw [LineSheafClassGroup318.classOf_inverse,LineSheafClassGroup318.classOf_inverse]
  exact congrArg (fun x => x⁻¹) (CartierIdealClass318.chart_independent I.subschemeι h h')
/-- The full ideal-sheaf equivalence and the actual glued-quotient Abel
map commute. This identifies constructions on all scheme tests; it does
not assume that the fppf target has a representing Jacobian scheme. -/
lemma ofDatum (D : ContactProjectiveQuotientData318.Datum R c)
    (hf : OriginalRegularIdealCover318.Property
      (CommRingCat.of (ContactProjectiveQuotientData318.finiteRing R c)) D.finiteIdeal)
    (hi : OriginalRegularIdealCover318.Property
      (CommRingCat.of (ContactProjectiveQuotientData318.infinityRing R c)) D.infinityIdeal) :
    ContactProjectiveAbelMap318.transformation R c D hf hi=
      transformation R c (ContactProjectiveIdealSheafEquiv318.toIdeal R c D)
        (ContactProjectiveCanonicalCartier318.regular_charts R c D hf hi) :=
  OriginalLineAbelTransformation318.class_congr p b
    (ContactProjectiveDivisorLine318.line R c D hf hi) _
    (ContactProjectiveCanonicalCartier318.divisor_class R c D hf hi)
end ContactProjectiveIdealAbel318
