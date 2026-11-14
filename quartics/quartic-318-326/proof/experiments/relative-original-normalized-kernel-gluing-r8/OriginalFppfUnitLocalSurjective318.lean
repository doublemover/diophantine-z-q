module
public import ContactDifferenceNaiveImage318
public section
noncomputable section
namespace OriginalFppfUnitLocalSurjective318
open AlgebraicGeometry CategoryTheory
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S)
/-- Local surjectivity of the ACTUAL canonical sheafification unit,
from the native concrete sheafification theorem for commutative groups.
It is local surjectivity only, never componentwise surjectivity or injectivity. -/
instance locallySurjective : Presheaf.IsLocallySurjective (RelativeFppfLineSheaf318.topology S)
    (RelativeFppfLineSheaf318.unit p) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (RelativeFppfLineSheaf318.topology S)
    (toSheafify (RelativeFppfLineSheaf318.topology S) (RelativeLineClassBaseChange318.presheaf p)))
end OriginalFppfUnitLocalSurjective318
