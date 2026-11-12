module
public import ContactProjectiveQuotientCartier318
public import CartierKernelEquality318
public import LineSheafClassGroup318
public section
noncomputable section
namespace ContactProjectiveDivisorLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
  (hf : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
  (hi : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal)
/-- O(D) is the actual inverse of the full closed kernel line O(-D).
No arbitrary input line is relabeled as the divisor line. -/
@[expose] def line : Line (ContactOriginalRelativePolynomialCharts318.curve R c) :=
  FramedLineInverse318.inverse (ContactProjectiveQuotientCartier318.idealLine R c D hf hi)
lemma class_eq : classOf (line R c D hf hi)=
    (CartierIdealClass318.value (ContactProjectiveQuotientGluing318.into R c D)
      (ContactProjectiveQuotientCartier318.regular_charts R c D hf hi))⁻¹ :=
  LineSheafClassGroup318.classOf_inverse _
lemma frames_independent
    (hf' : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
    (hi' : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal) :
    classOf (line R c D hf hi)=classOf (line R c D hf' hi') := by
  rw [class_eq,class_eq]
  exact congrArg (fun x => x⁻¹) (CartierIdealClass318.chart_independent
    (ContactProjectiveQuotientGluing318.into R c D)
    (ContactProjectiveQuotientCartier318.regular_charts R c D hf hi)
    (ContactProjectiveQuotientCartier318.regular_charts R c D hf' hi'))
end ContactProjectiveDivisorLine318
