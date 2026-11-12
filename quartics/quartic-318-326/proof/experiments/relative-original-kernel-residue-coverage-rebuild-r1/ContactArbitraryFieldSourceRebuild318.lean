module
public import ContactArbitraryKernelCoordinateRebuild318
public import ProjectiveKernelFieldSourceRebuild318
public import ContactOriginalGlobalKernelNormalizationRebuild318
public section
noncomputable section
namespace ContactArbitraryFieldSourceRebuild318
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

variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K] (f : R →ₐ[ℚ] K)
/-- A genuine whole field-test lift of the SAME original nonzero section. -/
def lift :
    letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
    ∀ a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] K,
      ContactArbitrarySectionParameter318.points R c L K f a ≠ 0 →
        (Spec K ⟶ ContactOriginalGlobalKernelNormalizationRebuild318.source R c L) := by
  letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
  intro a ha
  apply ProjectiveKernelFieldSourceRebuild318.lift R P Q d K a
  intro h
  apply ha
  change sections R c L K f (ProjectiveKernelParameter318.points R P Q d K a) = 0
  rw [h,map_zero]
@[reassoc] lemma lift_original :
    letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
    ∀ (a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] K)
      (ha : ContactArbitrarySectionParameter318.points R c L K f a ≠ 0),
      lift R c L K f a ha ≫ ContactOriginalGlobalKernelNormalizationRebuild318.original R c L =
        Spec.map (CommRingCat.ofHom a.toRingHom) := by
  letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
  intro a ha
  exact ProjectiveKernelFieldSourceRebuild318.lift_original R P Q d K a _
end ContactArbitraryFieldSourceRebuild318
