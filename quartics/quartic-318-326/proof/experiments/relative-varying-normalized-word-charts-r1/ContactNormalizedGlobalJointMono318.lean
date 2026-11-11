module
public import ContactNormalizedChartJointMono318
public section
noncomputable section
namespace ContactNormalizedGlobalJointMono318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "p" i => ContactNormalizedChartZeroFamily318.projection R c L hz i
local notation "u" => ProjectiveParameterSliceGluing318.into R P
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "proj" => ContactNormalizedZeroTransitions318.projection R c L hz
local notation "t" => ContactNormalizedZeroTransitions318.transition R c L hz

/-- The actual global family is jointly embedded by its ORIGINAL
contact-curve map and genuine normalized-parameter projection. The proof
uses the full target cover and the already constructed Cartesian squares. -/
lemma hom_ext {X : Scheme} (v w : X ⟶ ContactNormalizedGlobalZero318.scheme R c L hz)
    (hc : v ≫ ContactNormalizedGlobalOriginal318.original R c L hz=
      w ≫ ContactNormalizedGlobalOriginal318.original R c L hz)
    (hp : v ≫ ContactNormalizedZeroProjection318.projection R c L hz=
      w ≫ ContactNormalizedZeroProjection318.projection R c L hz) : v=w := by
  apply CoveredFamilyJointMono318.of_cover
    (ContactNormalizedGlobalOriginal318.original R c L hz)
    (ContactNormalizedZeroProjection318.projection R c L hz)
    (ContactNormalizedSectionParameter318.cover R c L hz)
    (ContactNormalizedChartZeroFamily318.scheme R c L hz)
    (ContactNormalizedGlobalZero318.into R c L hz)
    (ContactNormalizedChartZeroFamily318.projection R c L hz)
    (ContactNormalizedZeroCartesian318.square R c L hz) _ v w hc hp
  intro i X a b hc hp
  apply ContactNormalizedChartJointMono318.hom_ext R c L hz i a b
  · simpa only [ContactNormalizedGlobalOriginal318.into_original] using hc
  · exact hp
end ContactNormalizedGlobalJointMono318
