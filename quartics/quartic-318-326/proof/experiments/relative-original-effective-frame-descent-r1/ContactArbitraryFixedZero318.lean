module
public import ContactArbitraryCoefficientCongr318
public import ContactArbitraryTrivializationOpen318
public import AffineOpenAlgebraPoints318
public section
noncomputable section
namespace ContactArbitraryFixedZero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra ℚ (parameterRing R c L) :=
  ((algebraMap R (parameterRing R c L)).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R (parameterRing R c L) := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
variable (a : parameterRing R c L →ₐ[R] S)
local notation "g" => a.restrictScalars ℚ
lemma coefficient_base : g.comp (parameterCoefficient R c L)=f := by
  apply AlgHom.ext
  intro r
  exact a.commutes r

/-- Fixed original coefficient structures, not just isomorphic pulled
lines: the actual open factor criterion classifies THIS original section. -/
lemma factor_iff_empty :
    AffineOpenAlgebraPoints318.Factors R (parameterRing R c L) S
      (ContactArbitraryNowhereZeroOpen318.locus R c L) a ↔
    IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (L' R S f c L) (points R c L S f a)) :=
  (ContactArbitraryNowhereZeroPoints318.factor_iff_empty R c L S g).trans
    (ContactArbitraryCoefficientCongr318.empty_iff R c L S f
      (g.comp (parameterCoefficient R c L)) a
      (ContactHZeroCoefficientFunctor318.coefficientArrow R (CommRingCat.of (parameterRing R c L))
        (parameterCoefficient R c L) S g)
      (coefficient_base R c L S f a).symm rfl).symm
end ContactArbitraryFixedZero318
