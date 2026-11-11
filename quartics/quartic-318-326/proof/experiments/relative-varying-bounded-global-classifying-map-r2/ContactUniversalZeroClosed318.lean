module
public import ContactUniversalGlobalZero318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactUniversalZeroClosed318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

/-- The original universal global section has an actual closed zero
subscheme in the original parameter-family curve, including nilpotents. -/
instance closed : IsClosedImmersion (ContactUniversalGlobalZero318.into R c L hz) :=
  ContactGlobalZeroClosed318.closed _ c (universalLine R c L) (universalSection R c L hz)

@[expose] def idealSheaf : (curve (CommRingCat.of (parameterRing R c L)) c).IdealSheafData :=
  ContactGlobalZeroClosed318.idealSheaf _ c (universalLine R c L) (universalSection R c L hz)
@[expose] def subschemeIso : ContactUniversalGlobalZero318.scheme R c L hz ≅
    (idealSheaf R c L hz).subscheme :=
  ContactGlobalZeroClosed318.subschemeIso _ c (universalLine R c L) (universalSection R c L hz)
@[reassoc] lemma subschemeIso_into : (subschemeIso R c L hz).hom ≫
    (idealSheaf R c L hz).subschemeι = ContactUniversalGlobalZero318.into R c L hz :=
  ContactGlobalZeroClosed318.subschemeIso_into _ c (universalLine R c L) (universalSection R c L hz)
end ContactUniversalZeroClosed318
