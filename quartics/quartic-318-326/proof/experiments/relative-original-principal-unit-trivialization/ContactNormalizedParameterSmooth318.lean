module
public import ProjectiveParameterSchemeSmooth318
public import ContactNormalizedSectionParameter318
public section
noncomputable section
namespace ContactNormalizedParameterSmooth318
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

/-- The same global parameter carrying the original Cartier family and
Abel transformation is smooth over the original arbitrary base. This
is not a claim that its Abel map is smooth or that Picard is represented. -/
instance smooth : Smooth (ContactNormalizedSectionParameter318.projection R c L hz) :=
  ProjectiveParameterSchemeSmooth318.smooth R Γ(L.object,⊤)

theorem flat_lfp : Flat (ContactNormalizedSectionParameter318.projection R c L hz) ∧
    LocallyOfFinitePresentation (ContactNormalizedSectionParameter318.projection R c L hz) :=
  ⟨inferInstance,inferInstance⟩
end ContactNormalizedParameterSmooth318
