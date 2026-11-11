module
public import ProjectiveNormalizationLocalSections318
public import LaurentProjectionSmooth318
public section
noncomputable section
namespace ProjectiveNormalizationSmoothCover318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P

instance chart_smooth (i : Fin F.size) :
    Smooth (ProjectiveParameterPrincipalNormalization318.map R P i) := by
  letI : Smooth (ProjectivePrincipalLaurentScheme318.projection R P i) :=
    LaurentProjectionSmooth318.smooth (B i)
  rw [← ProjectivePrincipalLaurentScheme318.normalization R P i]
  infer_instance

/-- The SAME actual normalization from the original nonzero vector open
is smooth, using the full original principal-open cover and the literal
Laurent coefficient projections. -/
instance smooth : Smooth (ProjectiveParameterGlobalNormalization318.map R P) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth)
    (ProjectiveParameterPrincipalCover318.cover R P)
  intro i
  change Smooth (ProjectiveParameterPrincipalCover318.into R P i ≫
    ProjectiveParameterGlobalNormalization318.map R P)
  rw [ProjectiveParameterGlobalNormalization318.on_chart]
  infer_instance

/-- A genuine faithfully flat locally finitely presented normalization
cover, with actual local sections, for all original finite-projective
section modules. This is not a represented varying-line Picard functor. -/
theorem fppf_cover : Flat (ProjectiveParameterGlobalNormalization318.map R P) ∧
    Surjective (ProjectiveParameterGlobalNormalization318.map R P) ∧
    LocallyOfFinitePresentation (ProjectiveParameterGlobalNormalization318.map R P) :=
  ⟨inferInstance,ProjectiveNormalizationLocalSections318.surjective R P,inferInstance⟩
end ProjectiveNormalizationSmoothCover318
