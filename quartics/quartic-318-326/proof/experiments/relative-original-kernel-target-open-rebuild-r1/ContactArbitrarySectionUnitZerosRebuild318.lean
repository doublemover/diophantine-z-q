module
public import ProjectiveKernelScalarActionRebuild318
public import ContactArbitraryKernelCoordinateRebuild318
public import ContactZeroUnitScaling318
public section
noncomputable section
namespace ContactArbitrarySectionUnitZerosRebuild318
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
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤
/-- Actual section scaling on arbitrary original lines, without the old
H1-vanishing restriction of ContactParameterUnitZeros318. -/
lemma section_scaled :
    letI : Algebra R S := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R S f
    ∀ (u : Sˣ) (a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S),
      ContactArbitrarySectionParameter318.points R c L S f
        (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S (u:S) a) =
      (u:S) • ContactArbitrarySectionParameter318.points R c L S f a := by
  letI : Algebra R S := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R S f
  intro u a
  change sections R c L S f
    (ProjectiveKernelParameter318.points R P Q d S
      (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S (u:S) a)) = _
  rw [ProjectiveKernelScalarActionRebuild318.points_pointScale,map_smul] <;> rfl
/-- Equality of the ENTIRE original zero scheme, including nilpotents
and multiplicities; not just equality of its support. -/
lemma zero_scheme :
    letI : Algebra R S := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R S f
    ∀ (u : Sˣ) (a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S),
      ContactGlobalSectionZero318.scheme S c (L' R S f c L)
        (ContactArbitrarySectionParameter318.points R c L S f
          (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S (u:S) a)) =
      ContactGlobalSectionZero318.scheme S c (L' R S f c L)
        (ContactArbitrarySectionParameter318.points R c L S f a) := by
  letI : Algebra R S := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R S f
  intro u a
  rw [section_scaled]
  exact ContactZeroUnitScaling318.scheme_eq S c (L' R S f c L) u _
end ContactArbitrarySectionUnitZerosRebuild318
