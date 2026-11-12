module
public import CompactFiniteFlatRankBound318
public import ContactPositiveAbelPresentation318
public section
noncomputable section
namespace ContactNormalizedParameterCompact318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) := (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) := (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
/-- The actual normalized-section parameter has a FINITE affine cover
coming from the internally produced finite projective H0 frame. -/
instance compact : CompactSpace (ContactNormalizedSectionParameter318.scheme R c L hz) :=
  (ContactNormalizedSectionParameter318.cover R c L hz).compactSpace
@[expose] def bound : ℕ := CompactFiniteFlatRankBound318.bound (ContactNormalizedZeroProjection318.projection R c L hz)
lemma rank_bound (x : ContactNormalizedSectionParameter318.scheme R c L hz) :
    (ContactNormalizedZeroProjection318.projection R c L hz).finrank x≤bound R c L hz :=
  CompactFiniteFlatRankBound318.rank_bound _ x
end ContactNormalizedParameterCompact318
