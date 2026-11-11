module
public import ContactArbitrarySectionNaturality318
public section
noncomputable section
namespace ContactArbitraryUniversalSection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 ContactArbitrarySectionParameter318
open OriginalSectionPullbackComposition318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g : parameterRing R c L →ₐ[ℚ] S)

/-- The genuine universal section specializes by LITERAL geometric pullback, with
the original line associator, to the previously classified section. This closes
the native-specialization boundary of the arbitrary-line affine parameter. -/
lemma specialize :
    ContactHZeroCoefficientFunctor318.compositionSections R
      (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L S g
      (pull (curveMap (CommRingCat.of (parameterRing R c L)) S g c)
        (L' R (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) c L).object
        (universalSection R c L)) =
    points R c L S (g.comp (parameterCoefficient R c L))
      (ContactHZeroCoefficientFunctor318.coefficientArrow R
        (CommRingCat.of (parameterRing R c L)) (parameterCoefficient R c L) S g) := by
  simpa only [universalSection,AlgHom.comp_id] using
    ContactArbitrarySectionNaturality318.natural R (CommRingCat.of (parameterRing R c L)) S
      (parameterCoefficient R c L) g c L (AlgHom.id R _)
end ContactArbitraryUniversalSection318
