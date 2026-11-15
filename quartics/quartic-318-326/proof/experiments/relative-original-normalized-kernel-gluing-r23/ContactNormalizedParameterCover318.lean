module
public import ProjectiveParameterPositiveFibers318
public import ContactNormalizedParameterSmooth318
public section
noncomputable section
namespace ContactNormalizedParameterCover318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2

/-- With positive fibers of the ACTUAL original H0 module, the SAME
normalized parameter carrying the original effective divisor is a
surjective flat locally finitely presented morphism over the base.
Positivity is explicit; it is NOT silently inferred from H1 vanishing. -/
theorem flat_surjective_lfp
    (h : ProjectiveParameterPositiveFibers318.PositiveFibers R Γ(L.object,⊤)) :
    Flat (ContactNormalizedSectionParameter318.projection R c L hz) ∧
    Surjective (ContactNormalizedSectionParameter318.projection R c L hz) ∧
    LocallyOfFinitePresentation (ContactNormalizedSectionParameter318.projection R c L hz) :=
  ⟨inferInstance,ProjectiveParameterPositiveFibers318.surjective R Γ(L.object,⊤) h,inferInstance⟩
end ContactNormalizedParameterCover318
