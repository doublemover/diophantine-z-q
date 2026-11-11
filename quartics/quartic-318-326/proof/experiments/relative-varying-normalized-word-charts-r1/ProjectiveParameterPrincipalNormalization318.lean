module
public import ProjectiveParameterNormalizationNatural318
public section
noncomputable section
namespace ProjectiveParameterPrincipalNormalization318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (i : Fin F.size)
abbrev ring := Localization.Away (x i)
local notation "H" => ring R P i
instance baseAlgebra : Algebra R H := ((algebraMap A H).comp (algebraMap R A)).toAlgebra
instance baseTower : IsScalarTower R A H := IsScalarTower.of_algebraMap_eq' rfl
@[expose] def point : A →ₐ[R] H := IsScalarTower.toAlgHom R A H
@[expose] def unit : Hˣ where
  val := algebraMap A H (x i)
  inv := IsLocalization.Away.invSelf (x i)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]
lemma coordinate : point R P i (x i)=(unit R P i:H) := rfl

/-- The normalization map on the ACTUAL principal coordinate open of
the original affine section algebra. Its invertible coordinate and the
coordinate-one quotient are both constructed, not supplied by the caller. -/
@[expose] def map : Spec (CommRingCat.of H) ⟶ ProjectiveParameterSliceGluing318.scheme R P :=
  ProjectiveParameterNormalizedTest318.map R P (CommRingCat.of H)
    (point R P i) i (unit R P i) (coordinate R P i)

lemma over_base : map R P i ≫ ProjectiveParameterSliceBase318.projection R P=
    Spec.map (CommRingCat.ofHom (algebraMap R H)) :=
  ProjectiveParameterNormalizationNatural318.over_base R P (CommRingCat.of H)
    (point R P i) i (unit R P i) (coordinate R P i)
end ProjectiveParameterPrincipalNormalization318
