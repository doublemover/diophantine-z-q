module
public import ContactArbitrarySectionFinitePresentation318
public import FieldKernelParameterSmooth318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace ContactFieldArbitrarySectionSmooth318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionKernel318
open ContactOriginalRelativeLineOverlap318 ContactOriginalCoefficientActions318
open ContactArbitrarySectionParameter318
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve (CommRingCat.of K) c))
local notation "R" => CommRingCat.of K
local instance : Module K (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module K Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite K (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective K (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite K (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective K (oneTerm R c L) := (projective_terms R c L).2.2

instance algebra_smooth : Algebra.Smooth K (parameterRing R c L) :=
  FieldKernelParameterSmooth318.smooth K (zeroTerm R c L) (oneTerm R c L) (boundary R c L)

/-- Smoothness of the ORIGINAL full arbitrary-section parameter itself,
not merely a separately constructed H0 linear parameter. The original
line is fixed over the field; its H1 need not vanish. -/
instance smooth : Smooth (parameterProjection R c L) := by
  apply HasRingHomProperty.Spec_iff.mpr
  change (algebraMap K (parameterRing R c L)).Smooth
  exact RingHom.smooth_algebraMap.mpr inferInstance
end ContactFieldArbitrarySectionSmooth318
