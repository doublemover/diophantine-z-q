module
public import ProjectiveKernelGlobalNormalizationRebuild318
public import ProjectiveKernelNormalizedCover318
public section
noncomputable section
namespace ProjectiveKernelGlobalCoverRebuild318

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

open ProjectiveKernelNonzeroSourceRebuild318 ProjectiveKernelGlobalNormalizationRebuild318
/-- Smoothness on the actual full principal-source cover. -/
instance smooth : Smooth (map R P Q d) := by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth) (cover R P Q d)
  intro i
  change Smooth (chart R P Q d i≫map R P Q d)
  rw [on_chart]
  unfold ProjectiveKernelNormalizationAmbient318.localMap
  infer_instance
/-- Actual coordinate-one local section, not merely a residue-field lift. -/
def localSection (i : Fin F.size) :
    Spec (CommRingCat.of (ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i)) ⟶
      source R P Q d := ProjectiveKernelNormalizedCover318.section R P Q d i≫chart R P Q d i
@[reassoc] lemma section_map (i : Fin F.size) : localSection R P Q d i≫map R P Q d=
    ProjectiveKernelNormalizedGluing318.into R P Q d i := by
  rw [localSection,Category.assoc,on_chart,ProjectiveKernelNormalizationAmbient318.localMap,
    ←Category.assoc,ProjectiveKernelNormalizedCover318.section_projection,Category.id_comp]
instance surjective : Surjective (map R P Q d) := by
  constructor
  intro x
  obtain ⟨i,y,hy⟩ := ProjectiveKernelNormalizedGluing318.jointly_surjective R P Q d x
  refine ⟨localSection R P Q d i y,?_⟩
  exact (congrArg (fun k => k y) (section_map R P Q d i)).trans hy
/-- Genuine fppf normalization onto the represented normalized kernel,
not a cover of the coefficient base and not the varying Picard quotient. -/
lemma fppf : Flat (map R P Q d) ∧ Surjective (map R P Q d) ∧
    LocallyOfFinitePresentation (map R P Q d) := ⟨inferInstance,inferInstance,inferInstance⟩
end ProjectiveKernelGlobalCoverRebuild318
