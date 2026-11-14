module
public import ContactGlobalSectionZero318
public import ContactUniversalSectionZeros318
public section
noncomputable section
namespace ContactUniversalGlobalZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

/-- Global gluing of the ACTUAL universal section zeros on the original
contact family over the section-parameter algebra. Closed immersion,
Cartier regularity, finite flatness and degree are subsequent properties. -/
abbrev scheme : Scheme := ContactGlobalSectionZero318.scheme
  (CommRingCat.of (parameterRing R c L)) c (universalLine R c L) (universalSection R c L hz)
@[expose] def into : scheme R c L hz ⟶ curve (CommRingCat.of (parameterRing R c L)) c :=
  ContactGlobalSectionZero318.into _ c (universalLine R c L) (universalSection R c L hz)
@[expose] def projection : scheme R c L hz ⟶ parameterScheme R c L :=
  into R c L hz ≫ ContactRelativeStructuralHOne318.projection (CommRingCat.of (parameterRing R c L)) c

lemma full_zero_charts (x : scheme R c L hz) :
    (∃ a, ContactGlobalSectionZero318.finiteChart _ c (universalLine R c L)
      (universalSection R c L hz) a=x) ∨
    (∃ b, ContactGlobalSectionZero318.infinityChart _ c (universalLine R c L)
      (universalSection R c L hz) b=x) :=
  ContactGlobalSectionZero318.charts_cover _ _ _ _ x
end ContactUniversalGlobalZero318
