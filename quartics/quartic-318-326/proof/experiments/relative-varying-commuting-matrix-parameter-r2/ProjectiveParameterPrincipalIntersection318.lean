module
public import ProjectiveParameterPrincipalCompatibility318
public import MonicTargetPullback318
public import AffineAwayPullback318
public section
noncomputable section
namespace ProjectiveParameterPrincipalIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (i j : Fin F.size)
local notation "f" => CommRingCat.ofHom (algebraMap A (H i))
abbrev ring := AffineAwayPullback318.target f (x j)
local notation "K" => ring R P i j
instance baseAlgebra : Algebra R K := ((algebraMap (H i) K).comp (algebraMap R (H i))).toAlgebra
instance baseTower : IsScalarTower R (H i) K := IsScalarTower.of_algebraMap_eq' rfl
@[expose] def left : H i →ₐ[R] K := IsScalarTower.toAlgHom R (H i) K
@[expose] def right : H j →ₐ[R] K where
  __ := (AffineAwayPullback318.arrow f (x j)).hom
  commutes' r := by
    change (AffineAwayPullback318.arrow f (x j)).hom
      (algebraMap A (H j) (algebraMap R A r))=algebraMap (H i) K (algebraMap R (H i) r)
    rw [AffineAwayPullback318.arrow_base]
    rfl

lemma coefficients : (left R P i j).comp (ProjectiveParameterPrincipalNormalization318.point R P i)=
    (right R P i j).comp (ProjectiveParameterPrincipalNormalization318.point R P j) := by
  apply AlgHom.ext
  intro a
  exact (AffineAwayPullback318.arrow_base f (x j) a).symm

abbrev first : Spec K ⟶ ProjectiveParameterPrincipalCover318.chart R P i :=
  Spec.map (CommRingCat.ofHom (left R P i j).toRingHom)
abbrev second : Spec K ⟶ ProjectiveParameterPrincipalCover318.chart R P j :=
  Spec.map (CommRingCat.ofHom (right R P i j).toRingHom)

/-- The literal iterated localization is the ACTUAL intersection of the
original principal opens in the original nonzero parameter scheme. -/
lemma cartesian : IsPullback (first R P i j) (second R P i j)
    (ProjectiveParameterPrincipalCover318.into R P i)
    (ProjectiveParameterPrincipalCover318.into R P j) := by
  apply MonicTargetPullback318.cancel _ _ _ _ (ProjectiveParameterPrincipalCover318.locus R P).ι
  rw [ProjectiveParameterPrincipalCover318.into_affine,ProjectiveParameterPrincipalCover318.into_affine]
  exact AffineAwayPullback318.pullback f (x j)

lemma normalization : first R P i j ≫ ProjectiveParameterPrincipalNormalization318.map R P i=
    second R P i j ≫ ProjectiveParameterPrincipalNormalization318.map R P j :=
  ProjectiveParameterPrincipalCompatibility318.agree R P i j K (left R P i j) (right R P i j)
    (coefficients R P i j)
end ProjectiveParameterPrincipalIntersection318
