module
public import ContactArbitraryUniversalSection318
public import ContactGlobalZeroClosed318
public import ContactGlobalZeroFinitePresentation318
public import ContactRelativeOriginalSmoothProper318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactArbitraryUniversalZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

abbrev universalLine := L' R (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L
/-- The full actual universal zero scheme of an arbitrary original line. -/
abbrev scheme := ContactGlobalSectionZero318.scheme (CommRingCat.of (parameterRing R c L)) c
  (universalLine R c L) (universalSection R c L)
abbrev into : scheme R c L ⟶ curve (CommRingCat.of (parameterRing R c L)) c :=
  ContactGlobalSectionZero318.into _ c (universalLine R c L) (universalSection R c L)
abbrev projection : scheme R c L ⟶ parameterScheme R c L :=
  ContactGlobalResidueFlat318.projection _ c (universalLine R c L) (universalSection R c L)
instance closed : IsClosedImmersion (into R c L) := inferInstance
instance finitePresentation : LocallyOfFinitePresentation (into R c L) := inferInstance

/-- Properness is derived from the actual closed zero embedding and the SAME
original proper curve projection; zero-family flatness is neither assumed nor needed. -/
instance proper : IsProper (projection R c L) := by
  change IsProper (into R c L ≫ ContactRelativeStructuralHOne318.projection
    (CommRingCat.of (parameterRing R c L)) c)
  infer_instance
end ContactArbitraryUniversalZero318
