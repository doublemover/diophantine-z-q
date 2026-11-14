module
public import OriginalFrameDescentBaseChange318
public import ContactTrivializationChartClassification318
public section
noncomputable section
namespace ContactTrivializationActualDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local notation "N" => L' R S f c L
/-- Actual points of the SAME original trivialization-open parameter
are exactly the full finite/infinity frames whose two native restrictions
agree on their genuine categorical scheme intersection. -/
@[expose] def equivalence : ContactTrivializationAffinePoints318.Points R c L S f ≃
    OriginalFrameDescentData318.Data N (ContactOriginalFrameCover318.chartScheme S c)
      (ContactOriginalZeroKernelIso318.charts S c) :=
  (ContactTrivializationAffinePoints318.equivalence R c L S f).trans
    (OriginalFrameDescentData318.equivalence N (ContactOriginalFrameCover318.chartScheme S c)
      (ContactOriginalZeroKernelIso318.charts S c) (ContactOriginalFrameCover318.image_cover S c))
lemma original_frame (x : ContactTrivializationAffinePoints318.Points R c L S f) :
    (OriginalFrameDescentData318.equivalence N (ContactOriginalFrameCover318.chartScheme S c)
      (ContactOriginalZeroKernelIso318.charts S c) (ContactOriginalFrameCover318.image_cover S c)).symm
        (equivalence R c L S f x)=ContactTrivializationAffinePoints318.equivalence R c L S f x :=
  (OriginalFrameDescentData318.equivalence N (ContactOriginalFrameCover318.chartScheme S c)
    (ContactOriginalZeroKernelIso318.charts S c) (ContactOriginalFrameCover318.image_cover S c)).symm_apply_apply _
end ContactTrivializationActualDescent318
