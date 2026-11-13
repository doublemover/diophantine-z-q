module
public import ProjectiveKernelCoordinateDetectionRebuild318
public import ContactArbitrarySectionParameter318
public section
noncomputable section
namespace ContactArbitraryKernelCoordinateRebuild318
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

variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
@[instance_reducible] def coefficientAction : Algebra R S := f.toAlgebra
/-- Exact arbitrary-line section zero detection, with the named f action
installed explicitly in both statement and proof. -/
lemma section_zero_iff :
    letI : Algebra R S := coefficientAction R S f
    ∀ a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S,
      ContactArbitrarySectionParameter318.points R c L S f a = 0 ↔
        ∀ i, a (ProjectiveKernelCoordinateDetectionRebuild318.coordinate R P Q d i) = 0 := by
  letI : Algebra R S := coefficientAction R S f
  intro a
  change sections R c L S f (ProjectiveKernelParameter318.points R P Q d S a) = 0 ↔ _
  rw [(sections R c L S f).map_eq_zero_iff]
  exact ProjectiveKernelCoordinateDetectionRebuild318.kernel_zero_iff R P Q d S a
lemma section_nonzero_iff :
    letI : Algebra R S := coefficientAction R S f
    ∀ a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S,
      ContactArbitrarySectionParameter318.points R c L S f a ≠ 0 ↔
        ∃ i, a (ProjectiveKernelCoordinateDetectionRebuild318.coordinate R P Q d i) ≠ 0 := by
  letI : Algebra R S := coefficientAction R S f
  intro a
  rw [section_zero_iff R c L S f a]
  exact not_forall
end ContactArbitraryKernelCoordinateRebuild318
