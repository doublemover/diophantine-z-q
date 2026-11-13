module
public import ContactArbitrarySectionParameter318
public import ProjectiveKernelFinitePresentation318
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public section
noncomputable section
namespace ContactArbitrarySectionFinitePresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionKernel318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2

instance algebra_finitePresentation : Algebra.FinitePresentation R (parameterRing R c L) :=
  ProjectiveKernelFinitePresentation318.finitePresentation R (zeroTerm R c L) (oneTerm R c L)
    (boundary R c L)

/-- The ACTUAL original arbitrary-line section parameter is locally of
finite presentation over its original coefficient base. H1 may be nonzero. -/
instance locallyFinitePresentation : LocallyOfFinitePresentation (parameterProjection R c L) := by
  apply LocallyOfFinitePresentation.SpecMap_iff.mpr
  change (algebraMap R (parameterRing R c L)).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance
end ContactArbitrarySectionFinitePresentation318
