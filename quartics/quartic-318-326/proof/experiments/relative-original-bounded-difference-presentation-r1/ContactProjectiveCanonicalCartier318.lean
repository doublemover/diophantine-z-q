module
public import ContactProjectiveDivisorLine318
public import ContactProjectiveIdealSheafEquiv318
public import RegularClosedIso318
public section
noncomputable section
namespace ContactProjectiveCanonicalCartier318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactProjectiveQuotientData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
  (hf : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
  (hi : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal)
local notation "p" => ContactProjectiveQuotientGluing318.into R c D
local notation "I" => ContactProjectiveIdealSheafEquiv318.toIdeal R c D
local notation "h" => ContactProjectiveQuotientCartier318.regular_charts R c D hf hi
/-- Passing through the genuine ideal-sheaf classifier retains actual
Cartier quotient charts on its canonical closed subscheme. -/
lemma regular_charts : OriginalRegularClosedCharts318.Property I.subschemeι :=
  RegularClosedIso318.transport p I.subschemeι
    (ContactProjectiveQuotientIdealSheaf318.subschemeIso R c D)
    (ContactProjectiveQuotientIdealSheaf318.subschemeIso_into R c D) h
@[expose] def kernelIso : (ActualCartierIdealLine318.line p h).object ≅
    (ActualCartierIdealLine318.line I.subschemeι (regular_charts R c D hf hi)).object :=
  CartierKernelEquality318.iso p I.subschemeι h (regular_charts R c D hf hi) I.ker_subschemeι.symm
lemma divisor_class : classOf (ContactProjectiveDivisorLine318.line R c D hf hi)=
    classOf (FramedLineInverse318.inverse
      (ActualCartierIdealLine318.line I.subschemeι (regular_charts R c D hf hi))) := by
  change classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line p h))=_
  rw [LineSheafClassGroup318.classOf_inverse,LineSheafClassGroup318.classOf_inverse]
  exact congrArg (fun x => x⁻¹) (LineSheafClass318.classOf_eq (kernelIso R c D hf hi))
end ContactProjectiveCanonicalCartier318
