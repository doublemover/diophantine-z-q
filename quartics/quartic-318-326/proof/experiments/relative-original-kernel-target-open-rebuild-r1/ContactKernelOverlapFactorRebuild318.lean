module
public import ProjectiveKernelOverlapOriginalRebuild318
public import ContactKernelPrincipalSaturationRebuild318
public section
noncomputable section
namespace ContactKernelOverlapFactorRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
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
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "D" => ProjectiveKernelOverlapAlgebras318.ring R P Q d
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
lemma unit_factor :
    letI : Algebra R S := f.toAlgebra
    ∀ (a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S) (u : Sˣ),
      (∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L = Spec.map (CommRingCat.ofHom
          (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S (u:S) a).toRingHom)) ↔
      ∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L = Spec.map (CommRingCat.ofHom a.toRingHom) := by
  letI : Algebra R S := f.toAlgebra
  intro a u
  rw [ContactArbitraryAffineNowhereZeroRebuild318.factor_iff_empty R c L S f,
    ContactArbitraryAffineNowhereZeroRebuild318.factor_iff_empty R c L S f,
    ContactArbitrarySectionUnitZerosRebuild318.zero_scheme]
/-- All coefficient-ring points on the exact overlap, with its full
quotient equations and the original two line-section parameters. -/
lemma factor_iff :
    letI : Algebra R S := f.toAlgebra
    ∀ (i j : Fin F.size) (a : D i j →ₐ[R] S),
      (∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L = Spec.map (CommRingCat.ofHom
          (a.comp (ProjectiveKernelOverlapOriginalRebuild318.rightPoint R P Q d i j)).toRingHom)) ↔
      ∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L = Spec.map (CommRingCat.ofHom
          (a.comp (ProjectiveKernelOverlapOriginalRebuild318.leftPoint R P Q d i j)).toRingHom) := by
  letI : Algebra R S := f.toAlgebra
  intro i j a
  rw [ProjectiveKernelOverlapOriginalRebuild318.right_scaled,ProjectiveKernelScalarNaturalRebuild318.natural]
  exact unit_factor R c L S f _
    (Units.map a.toMonoidHom (ProjectiveKernelOverlapOriginalRebuild318.ratio R P Q d i j))
end ContactKernelOverlapFactorRebuild318
