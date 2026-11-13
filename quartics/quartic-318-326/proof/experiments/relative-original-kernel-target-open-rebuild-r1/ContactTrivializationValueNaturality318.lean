module
public import ContactTrivializationAffinePoints318
public import AffineOpenPointNaturality318
public section
noncomputable section
namespace ContactTrivializationValueNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318 ContactTrivializationAffinePoints318
open OriginalSectionPullbackComposition318
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local notation "U" => ContactArbitraryNowhereZeroOpen318.locus R c L
local notation "φ" => ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g

/-- Naturality for literal scheme precomposition and genuine geometric
section pullback, including the original coefficient-line associator.
Since full unit maps are determined by this value, no abstract transport
of trivializations replaces their original maps. -/
lemma value_natural (x : Points R c L S f) :
    ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
      (pull (ContactRelativeCoefficientChange318.curveMap S T g c) (L' R S f c L).object
        ((equivalence R c L S f x).hom.app ⊤ 1))=
    (equivalence R c L T (g.comp f)
      (AffineOpenPointNaturality318.map R (parameterRing R c L) S T U φ x)).hom.app ⊤ 1 := by
  rw [ContactTrivializationAffinePoints318.value,ContactTrivializationAffinePoints318.value,
    AffineOpenPointNaturality318.coordinate_map]
  exact (ContactArbitrarySectionNaturality318.natural R S T f g c L
    (AffineOpenAlgebraPoints318.coordinate R (parameterRing R c L) S U x))
end ContactTrivializationValueNaturality318
