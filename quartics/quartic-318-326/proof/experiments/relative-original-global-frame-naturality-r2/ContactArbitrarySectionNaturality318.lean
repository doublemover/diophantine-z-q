module
public import ContactSectionKernelGeometric318
public import ContactArbitrarySectionParameter318
public section
noncomputable section
namespace ContactArbitrarySectionNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318 ContactOriginalSectionKernel318
open ContactArbitrarySectionParameter318 OriginalSectionPullbackComposition318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2

/-- The original section point equivalence is now natural for the ACTUAL geometric
pullback and original coefficient-composition isomorphism on every test algebra. -/
lemma natural (a : parameterRing R c L →ₐ[R] S) :
    ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
      (pull (curveMap S T g c) (L' R S f c L).object (points R c L S f a)) =
    points R c L T (g.comp f)
      ((ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g).comp a) := by
  change ContactHZeroCoefficientFunctor318.compositionSections R S f c L T g
    (pull _ _ (sections R c L S f (ProjectiveKernelParameter318.points R _ _ _ S a))) = _
  rw [ContactSectionKernelGeometric318.natural]
  rw [← ProjectiveKernelNaturality318.natural]
  rfl
end ContactArbitrarySectionNaturality318
