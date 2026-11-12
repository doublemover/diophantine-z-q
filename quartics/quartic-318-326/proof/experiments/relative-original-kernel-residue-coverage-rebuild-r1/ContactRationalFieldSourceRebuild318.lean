module
public import ContactNowhereZeroFieldNormalizationRebuild318
public import ContactArbitraryZeroSpecialization318
public section
noncomputable section
namespace ContactRationalFieldSourceRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K]
  (g : parameterRing R c L →ₐ[ℚ] K)
/-- The exact geometric specialization supplies a lift of this same
rational parameter point. The named R-action is installed explicitly. -/
def data (h : IsEmpty ↑(pullback (ContactArbitraryUniversalZero318.projection R c L)
    (Spec.map (CommRingCat.ofHom g.toRingHom)))) :
    {a : Spec K ⟶ ContactOriginalGlobalKernelNormalizationRebuild318.source R c L //
      a ≫ ContactOriginalGlobalKernelNormalizationRebuild318.original R c L =
        Spec.map (CommRingCat.ofHom g.toRingHom)} := by
  let f := g.comp (parameterCoefficient R c L)
  letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
  let a : parameterRing R c L →ₐ[R] K :=
    ContactHZeroCoefficientFunctor318.coefficientArrow R (CommRingCat.of (parameterRing R c L))
      (parameterCoefficient R c L) K g
  have he := (ContactArbitraryZeroSpecialization318.empty_iff R c L K g).mpr h
  exact ⟨ContactNowhereZeroFieldNormalizationRebuild318.sourceLift R c L K f a he,
    ContactNowhereZeroFieldNormalizationRebuild318.sourceLift_original R c L K f a he⟩
end ContactRationalFieldSourceRebuild318
