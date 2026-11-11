module
public import ContactUniversalZeroClosed318
public import ContactGlobalZeroFinitePresentation318
public section
noncomputable section
namespace ContactUniversalZeroFinitePresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

/-- The SAME actual universal zero closed immersion is locally of finite
presentation. This is over the original contact parameter-family curve;
it does not assert flatness or a fixed degree over the parameter base. -/
instance finitePresentation : LocallyOfFinitePresentation (ContactUniversalGlobalZero318.into R c L hz) :=
  ContactGlobalZeroFinitePresentation318.finitePresentation _ c (universalLine R c L) (universalSection R c L hz)
end ContactUniversalZeroFinitePresentation318
