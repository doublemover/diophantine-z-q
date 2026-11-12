module
public import ProjectiveKernelNonzeroSourceRebuild318
public import SchemeMonoLocalLift318
public section
noncomputable section
namespace ProjectiveKernelGlobalNormalizationRebuild318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "K" => ProjectiveKernelParameter318.algebra R P Q d
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "W" => ProjectiveParameterPrincipalCover318.locus R P
local notation "U" => ProjectiveParameterPrincipalCover318.cover R P
local notation "Z" => fun i : Fin F.size =>
  Spec (CommRingCat.of (ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i))

open ProjectiveKernelNonzeroSourceRebuild318
local notation "J" => ProjectiveKernelNormalizedGluing318.closedInto R P Q d
local notation "N" => ProjectiveKernelNormalizedGluing318.scheme R P Q d
local notation "n" => ProjectiveKernelNormalizationAmbient318.localMap R P Q d
local notation "f" => ambient R P Q d≫ProjectiveParameterGlobalNormalization318.map R P
lemma local_factor (i : Fin F.size) : n i≫J=chart R P Q d i≫f := by
  rw [ProjectiveKernelNormalizationAmbient318.localMap_ambient,←Category.assoc,
    chart_ambient,Category.assoc,ProjectiveParameterGlobalNormalization318.on_chart] <;> rfl
/-- Actual global normalization of the unchanged nonzero kernel source.
It is glued through the produced closed immersion, not an assumed quotient. -/
def map : source R P Q d ⟶ N :=
  SchemeMonoLocalLift318.lift (cover R P Q d) J f n (local_factor R P Q d)
@[reassoc] lemma on_chart (i : Fin F.size) : chart R P Q d i≫map R P Q d=n i :=
  SchemeMonoLocalLift318.into_lift _ _ _ _ _ i
@[reassoc] lemma factor : map R P Q d≫J=f :=
  SchemeMonoLocalLift318.lift_factor _ _ _ _ _
lemma unique (g : source R P Q d ⟶ N) (hg : g≫J=f) : g=map R P Q d :=
  SchemeMonoLocalLift318.unique _ _ _ _ _ g hg
/-- The literal coefficient map of the original full kernel algebra. -/
lemma over_base : map R P Q d≫ProjectiveKernelNormalizedGluing318.projection R P Q d=
    original R P Q d≫Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  change map R P Q d≫J≫ProjectiveParameterSliceBase318.projection R P=_
  rw [←Category.assoc,factor,Category.assoc,ProjectiveParameterGlobalNormalization318.over_base,
    ←Category.assoc,←pullback.condition,Category.assoc]
  congr 1
  rw [ambientInto,←Spec.map_comp]
  rfl
end ProjectiveKernelGlobalNormalizationRebuild318
