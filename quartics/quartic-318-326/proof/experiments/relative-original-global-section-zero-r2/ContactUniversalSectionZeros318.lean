module
public import ContactOriginalSectionParameter318
public import ContactOriginalSectionZeros318
public section
noncomputable section
namespace ContactUniversalSectionZeros318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl

/-- Actual zero quotient schemes of the universal original GLOBAL section
on the full finite chart, infinity chart and their original intersection.
Regularity, a Cartier divisor and the global glued zero scheme are separate. -/
@[expose] def finiteZero : Scheme := ContactOriginalSectionZeros318.finiteZero
  (CommRingCat.of (parameterRing R c L)) c (universalLine R c L) (universalSection R c L hz)
@[expose] def infinityZero : Scheme := ContactOriginalSectionZeros318.infinityZero
  (CommRingCat.of (parameterRing R c L)) c (universalLine R c L) (universalSection R c L hz)
@[expose] def overlapZero : Scheme := ContactOriginalSectionZeros318.overlapZero
  (CommRingCat.of (parameterRing R c L)) c (universalLine R c L) (universalSection R c L hz)

/-- Exact equality of the TWO extended universal section ideals over the
whole original parameter-family Laurent overlap. -/
lemma same_overlap :
    Ideal.map (ContactOriginalRelativeLineOverlap318.finiteArrow (CommRingCat.of (parameterRing R c L)) c).hom
      (ContactOriginalSectionZeros318.finiteIdeal (CommRingCat.of (parameterRing R c L)) c
        (universalLine R c L) (universalSection R c L hz)) =
    Ideal.map (ContactOriginalRelativeLineOverlap318.infinityArrow (CommRingCat.of (parameterRing R c L)) c).hom
      (ContactOriginalSectionZeros318.infinityIdeal (CommRingCat.of (parameterRing R c L)) c
        (universalLine R c L) (universalSection R c L hz)) :=
  ContactOriginalSectionZeros318.same_overlap (CommRingCat.of (parameterRing R c L)) c
    (universalLine R c L) (universalSection R c L hz)
end ContactUniversalSectionZeros318
