module
public import ContactArbitraryFieldSourceRebuild318
public import ContactZeroSectionNonemptyRebuild318
public section
noncomputable section
namespace ContactNowhereZeroFieldNormalizationRebuild318
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
/-- Empty full original zero scheme supplies the needed nonzero input;
no nonzero-section premise is assumed here. This is still a FIELD-test
producer, not a claim that the whole nowhere-zero open has descended. -/
def sourceLift :
    letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
    ∀ a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] K,
      IsEmpty ↑(ContactGlobalSectionZero318.scheme K c (L' R K f c L)
        (ContactArbitrarySectionParameter318.points R c L K f a)) →
      (Spec K ⟶ ContactOriginalGlobalKernelNormalizationRebuild318.source R c L) := by
  letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
  intro a ha
  exact ContactArbitraryFieldSourceRebuild318.lift R c L K f a
    (ContactZeroSectionNonemptyRebuild318.nonzero_of_empty K c _ _ ha)
@[reassoc] lemma sourceLift_original :
    letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
    ∀ (a : ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] K)
      (ha : IsEmpty ↑(ContactGlobalSectionZero318.scheme K c (L' R K f c L)
        (ContactArbitrarySectionParameter318.points R c L K f a))),
      sourceLift R c L K f a ha ≫ ContactOriginalGlobalKernelNormalizationRebuild318.original R c L =
        Spec.map (CommRingCat.ofHom a.toRingHom) := by
  letI : Algebra R K := ContactArbitraryKernelCoordinateRebuild318.coefficientAction R K f
  intro a ha
  exact ContactArbitraryFieldSourceRebuild318.lift_original R c L K f a _
end ContactNowhereZeroFieldNormalizationRebuild318
