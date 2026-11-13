module
public import ProjectiveKernelNormalizedPointScaleRebuild318
public import ContactArbitrarySectionUnitZerosRebuild318
public import ContactArbitraryAffineNowhereZeroRebuild318
public section
noncomputable section
namespace ContactKernelPrincipalSaturationRebuild318
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

local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
/-- The actual principal kernel point and its original normalized slice
point have the SAME whole zero scheme over every coefficient ring. -/
lemma zero_scheme :
    letI : Algebra R S := f.toAlgebra
    ∀ (i : Fin F.size) (a : ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i →ₐ[R] S),
      ContactGlobalSectionZero318.scheme S c (L' R S f c L)
        (ContactArbitrarySectionParameter318.points R c L S f
          (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i))) =
      ContactGlobalSectionZero318.scheme S c (L' R S f c L)
        (ContactArbitrarySectionParameter318.points R c L S f
          ((ProjectiveKernelNormalizedAlgebras318.points R P Q d i S a).2.comp
            (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i))) := by
  letI : Algebra R S := f.toAlgebra
  intro i a
  rw [ProjectiveKernelNormalizedPointScaleRebuild318.original_scaled,
    ContactArbitrarySectionUnitZerosRebuild318.zero_scheme]
/-- True unit-saturation on ALL affine tests, with the original
nowhere-zero open and both actual parameter ring maps retained. -/
lemma factor_iff :
    letI : Algebra R S := f.toAlgebra
    ∀ (i : Fin F.size) (a : ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i →ₐ[R] S),
      (∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L =
          Spec.map (CommRingCat.ofHom
            (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)).toRingHom)) ↔
      (∃ h : Spec S ⟶ ContactArbitraryNowhereZeroOpen318.scheme R c L,
        h ≫ ContactArbitraryNowhereZeroOpen318.into R c L =
          Spec.map (CommRingCat.ofHom
            ((ProjectiveKernelNormalizedAlgebras318.points R P Q d i S a).2.comp
              (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i)).toRingHom)) := by
  letI : Algebra R S := f.toAlgebra
  intro i a
  rw [ContactArbitraryAffineNowhereZeroRebuild318.factor_iff_empty R c L S f,
    ContactArbitraryAffineNowhereZeroRebuild318.factor_iff_empty R c L S f,
    zero_scheme R c L S f i a]
end ContactKernelPrincipalSaturationRebuild318
