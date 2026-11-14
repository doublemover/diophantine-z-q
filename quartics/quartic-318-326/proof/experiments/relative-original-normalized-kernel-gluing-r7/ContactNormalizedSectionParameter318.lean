module
public import ProjectiveParameterSliceBase318
public import ContactOriginalSectionParameter318
public section
noncomputable section
namespace ContactNormalizedSectionParameter318
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

/-- The global normalized-section parameter SCHEME for the literal
original contact line, constructed from its actual whole H0 module.
No free basis or represented Picard scheme is assumed. -/
abbrev scheme : Scheme := ProjectiveParameterSliceGluing318.scheme R Γ(L.object,⊤)
abbrev projection : scheme R c L hz ⟶ Spec R :=
  ProjectiveParameterSliceBase318.projection R Γ(L.object,⊤)
abbrev cover : (scheme R c L hz).OpenCover :=
  ProjectiveParameterSliceGluing318.cover R Γ(L.object,⊤)

/-- Every genuine original line has a positive twist to which this
construction applies, by the existing actual H1 vanishing producer.
This does not identify different twists or assert Picard representability. -/
theorem exists_positive_bound : ∃ b : ℕ,
    ∀ x : NonreducedLineMayerVietoris318.H1
      (ContactRelativeGeometricTwist318.twist R c L ((b+1:ℕ):ℤ)),x=0 :=
  ContactPositiveSectionParameter318.exists_positive_bound R c L
end ContactNormalizedSectionParameter318
