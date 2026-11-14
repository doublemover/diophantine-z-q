module
public import ContactOriginalLaurentStabilizer318
public import LaurentProjectionSmooth318
public section
noncomputable section
namespace ContactOriginalSmoothStabilizer318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L L
/-- Smoothness of the ORIGINAL stabilizer projection, transported from
its actual Laurent-spectrum isomorphism, not an assumed torsor atlas. -/
instance smooth : Smooth q := by
  haveI : Smooth (LaurentWholeUnitRepresentation318.projection R) :=
    LaurentProjectionSmooth318.smooth R
  rw [←ContactOriginalLaurentStabilizer318.hom_base R c L]
  infer_instance
instance flat : Flat q := inferInstance
instance presentation : LocallyOfFinitePresentation q := inferInstance
instance affine : IsAffineHom q := by
  rw [←ContactOriginalLaurentStabilizer318.hom_base R c L]
  infer_instance

end ContactOriginalSmoothStabilizer318
