module
public import ProjectiveParameterPrincipalCover318
public section
noncomputable section
namespace ProjectiveParameterPrincipalCompatibility318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "point" => ProjectiveParameterPrincipalNormalization318.point R P
local notation "unit" => ProjectiveParameterPrincipalNormalization318.unit R P
variable (i j : Fin F.size) (T : CommRingCat.{0}) [Algebra R T]
  (f : H i →ₐ[R] T) (g : H j →ₐ[R] T)
  (h : f.comp (point i)=g.comp (point j))

/-- The principal normalization maps agree on every ACTUAL common
coefficient test. Both selected coordinates remain units after arbitrary
base change; the equality uses full original algebra maps, not supports. -/
lemma agree : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    ProjectiveParameterPrincipalNormalization318.map R P i=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      ProjectiveParameterPrincipalNormalization318.map R P j := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    ProjectiveParameterNormalizedTest318.map R P (CommRingCat.of (H i)) (point i) i
      (unit i) (ProjectiveParameterPrincipalNormalization318.coordinate R P i)=_
  rw [ProjectiveParameterNormalizationNatural318.map_natural]
  change ProjectiveParameterNormalizedTest318.map R P T (f.comp (point i)) i
    (Units.map f.toMonoidHom (unit i)) _=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      ProjectiveParameterNormalizedTest318.map R P (CommRingCat.of (H j)) (point j) j
        (unit j) (ProjectiveParameterPrincipalNormalization318.coordinate R P j)
  rw [ProjectiveParameterNormalizationNatural318.map_natural]
  have hj : (f.comp (point i)) (ProjectiveParameterZeroCoordinates318.coordinate R P j)=
      (Units.map g.toMonoidHom (unit j):T) := by
    rw [h]
    exact ProjectiveParameterNormalizationNatural318.coordinate R P (CommRingCat.of (H j)) T g
      (point j) j (unit j) (ProjectiveParameterPrincipalNormalization318.coordinate R P j)
  simpa only [h] using ProjectiveParameterNormalizedTest318.independent R P T (f.comp (point i))
    i j (Units.map f.toMonoidHom (unit i)) (Units.map g.toMonoidHom (unit j))
    (ProjectiveParameterNormalizationNatural318.coordinate R P (CommRingCat.of (H i)) T f
      (point i) i (unit i) (ProjectiveParameterPrincipalNormalization318.coordinate R P i)) hj
end ProjectiveParameterPrincipalCompatibility318
