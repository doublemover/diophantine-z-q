module
public import ProjectiveKernelGlobalCoverRebuild318
public section
noncomputable section
namespace ContactOriginalGlobalKernelNormalizationRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318 ContactOriginalSectionKernel318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2
local notation "P" => zeroTerm R c L
local notation "Q" => oneTerm R c L
local notation "d" => boundary R c L
abbrev source : Scheme := ProjectiveKernelNonzeroSourceRebuild318.source R P Q d
/-- The actual original arbitrary-line section parameter remains the source. -/
abbrev original : source R c L ⟶ ContactArbitrarySectionParameter318.parameterScheme R c L :=
  ProjectiveKernelNonzeroSourceRebuild318.original R P Q d
abbrev normalize : source R c L ⟶ ContactOriginalNormalizedKernelScheme318.scheme R c L :=
  ProjectiveKernelGlobalNormalizationRebuild318.map R P Q d
instance smooth : Smooth (normalize R c L) := inferInstance
instance surjective : Surjective (normalize R c L) := inferInstance
lemma coefficient : normalize R c L≫ContactOriginalNormalizedKernelScheme318.projection R c L=
    original R c L≫Spec.map (CommRingCat.ofHom
      (algebraMap R (ProjectiveKernelParameter318.algebra R P Q d))) :=
  ProjectiveKernelGlobalNormalizationRebuild318.over_base R P Q d
/-- No projectivity or local freeness of H0 or the differential kernel
is asserted. Only the original finite-projective two-term presentation is used. -/
lemma fppf : Flat (normalize R c L) ∧ Surjective (normalize R c L) ∧
    LocallyOfFinitePresentation (normalize R c L) :=
  ProjectiveKernelGlobalCoverRebuild318.fppf R P Q d
end ContactOriginalGlobalKernelNormalizationRebuild318
