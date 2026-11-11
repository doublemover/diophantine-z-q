module
public import ContactNormalizedAbelFiber318
public import ContactNormalizedAbelMap318
public import OriginalAbelSheafValue318
public section
noncomputable section
namespace ContactNormalizedAbelTransformationFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz

/-- On every scheme test, including arbitrary nonreduced schemes, the
Abel transformation of the ACTUAL normalized effective divisor family
is exactly the transformation induced by the ORIGINAL pulled line.
Thus this constructed parameter occupies the correct fixed-line Abel
fiber; it is not mistakenly called a varying-line Picard parameter. -/
theorem original_transformation : ContactNormalizedAbelMap318.transformation R c L hz=
    OriginalLineAbelTransformation318.transformation p b
      (LineSheafPullback318.line (pullback.fst p b) L) := by
  apply OriginalAbelSheafValue318.value_congr
  exact ContactNormalizedAbelFiber318.original_sheaf_class R c L hz
end ContactNormalizedAbelTransformationFiber318
