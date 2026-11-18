module
public import RelativeClassBaseTwistIso318
public section
noncomputable section
namespace OriginalFppfUnitLocalInjective318
open AlgebraicGeometry CategoryTheory
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S)
/-- Native LOCAL injectivity of the actual canonical unit. -/
instance locallyInjective : Presheaf.IsLocallyInjective (RelativeFppfLineSheaf318.topology S)
    (RelativeFppfLineSheaf318.unit p) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (RelativeFppfLineSheaf318.topology S)
    (toSheafify (RelativeFppfLineSheaf318.topology S) (RelativeLineClassBaseChange318.presheaf p)))
end OriginalFppfUnitLocalInjective318
