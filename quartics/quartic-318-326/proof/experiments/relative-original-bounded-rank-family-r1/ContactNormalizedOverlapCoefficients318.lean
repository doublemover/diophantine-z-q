module
public import ContactUnitZeroPullback318
public import ContactNormalizedChartZeroIdentification318
public section
noncomputable section
namespace ContactNormalizedOverlapCoefficients318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ProjectiveParameterSliceLocalization318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (i j : Fin F.size)
abbrev ring := CommRingCat.of (algebra R P i j)
local notation "S" => ring R c L hz i j
instance rationalAlgebra : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
instance rationalTower : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl

/-- The first normalized parameter is the literal quotient/localization
map; the other is induced by the actual opposite-slice embedding. -/
@[expose] def first : A →ₐ[ℚ] S := (point R P i j).restrictScalars ℚ
@[expose] def second : A →ₐ[ℚ] S :=
  ((oppositeSlice R P i j).comp
    (Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P j))).restrictScalars ℚ

/-- The overlap transition scales the original classifier by the actual
inverse of x_j, which is a unit in this SAME localization, even over a
nonreduced coefficient ring. -/
lemma second_scaled : second R c L hz i j=
    ContactClassifiedUnitZero318.scaledCoefficient R c L S
      (first R c L hz i j) (unit R P i j)⁻¹ := by
  apply AlgHom.ext
  intro a
  exact oppositeSlice_mk R P i j a

@[expose] def zeroIso :
    CategoryTheory.Limits.pullback (ContactUniversalGlobalZero318.projection R c L hz)
      (Spec.map (CommRingCat.ofHom (second R c L hz i j).toRingHom)) ≅
    CategoryTheory.Limits.pullback (ContactUniversalGlobalZero318.projection R c L hz)
      (Spec.map (CommRingCat.ofHom (first R c L hz i j).toRingHom)) :=
  ContactUnitZeroPullback318.iso R c L hz S (first R c L hz i j)
    (second R c L hz i j) (unit R P i j)⁻¹ (second_scaled R c L hz i j)
@[reassoc] lemma zeroIso_projection : (zeroIso R c L hz i j).hom ≫
    CategoryTheory.Limits.pullback.snd _ _=CategoryTheory.Limits.pullback.snd _ _ :=
  ContactUnitZeroPullback318.iso_projection R c L hz S (first R c L hz i j)
    (second R c L hz i j) (unit R P i j)⁻¹ (second_scaled R c L hz i j)
end ContactNormalizedOverlapCoefficients318
