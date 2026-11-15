module
public import ContactOriginalFrameCover318
public import ContactTrivializationFullNaturality318
public section
noncomputable section
namespace ContactTrivializationChartClassification318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local notation "N" => L' R S f c L
/-- The SAME actual trivialization-open scheme points classify compatible
FULL original finite/infinity chart frames, with both inverse maps.
This is an actual consumer of effective frame descent, not a class quotient. -/
@[expose] def equivalence : ContactTrivializationAffinePoints318.Points R c L S f ≃
    {e : OriginalFrameCoverSections318.LocalFrames N
      (ContactOriginalFrameCover318.chartScheme S c) (ContactOriginalZeroKernelIso318.charts S c) //
      OriginalFrameCoverSections318.Compatible N
        (ContactOriginalFrameCover318.chartScheme S c) (ContactOriginalZeroKernelIso318.charts S c) e} :=
  (ContactTrivializationAffinePoints318.equivalence R c L S f).trans
    (ContactOriginalFrameCover318.equivalence S c N)
lemma recover (x : ContactTrivializationAffinePoints318.Points R c L S f) :
    (ContactOriginalFrameCover318.equivalence S c N).symm
      (equivalence R c L S f x)=ContactTrivializationAffinePoints318.equivalence R c L S f x :=
  (ContactOriginalFrameCover318.equivalence S c N).symm_apply_apply _
end ContactTrivializationChartClassification318
