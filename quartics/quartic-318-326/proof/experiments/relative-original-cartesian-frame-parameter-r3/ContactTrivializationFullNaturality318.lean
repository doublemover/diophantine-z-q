module
public import OriginalFramePullbackUnits318
public import ContactTrivializationValueNaturality318
public section
noncomputable section
namespace ContactTrivializationFullNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactTrivializationAffinePoints318
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local notation "U" => ContactArbitraryNowhereZeroOpen318.locus R c L
local notation "φ" => ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g

/-- Equality of the ENTIRE original frame isomorphisms, not only classes
or values: represented scheme precomposition equals genuine pullback,
including the literal coefficient-composition sheaf comparison. -/
lemma natural (x : Points R c L S f) :
    OriginalFramePullback318.frame (ContactRelativeCoefficientChange318.curveMap S T g c)
      (L' R S f c L) (equivalence R c L S f x) ≪≫
        ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L=
    equivalence R c L T (g.comp f)
      (AffineOpenPointNaturality318.map R (ContactArbitrarySectionParameter318.parameterRing R c L)
        S T U φ x) := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom.app ⊤
    ((OriginalFramePullback318.frame (ContactRelativeCoefficientChange318.curveMap S T g c)
      (L' R S f c L) (equivalence R c L S f x)).hom.app ⊤ 1)=_
  rw [OriginalFramePullback318.value]
  exact ContactTrivializationValueNaturality318.value_natural R S T f g c L x
end ContactTrivializationFullNaturality318
