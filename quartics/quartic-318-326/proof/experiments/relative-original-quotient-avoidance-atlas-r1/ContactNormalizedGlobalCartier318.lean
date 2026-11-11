module
public import ContactNormalizedZeroCartierSquare318
public section
noncomputable section
namespace ContactNormalizedGlobalCartier318
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

/-- The SAME global normalized zero embedding has actual Cartier
quotient charts over every point of the ORIGINAL relative ambient curve.
All normalized coefficient tests and their full Cartesian embedding
squares are constructed; no local regularity premise remains. -/
theorem regular_charts : OriginalRegularClosedCharts318.Property
    (ContactNormalizedGlobalClosedFamily318.into R c L hz) := by
  apply OriginalRegularClosedCharts318.glue
    (ContactNormalizedGlobalClosedFamily318.into R c L hz)
    (fun i : Fin F.size => curve (ContactNormalizedCartierTest318.ring R c L hz i) c)
    (ContactNormalizedCartierTest318.scheme R c L hz)
    (ContactNormalizedAmbientCharts318.into R c L hz)
    (ContactNormalizedCartierTest318.into R c L hz)
    (ContactNormalizedZeroCartierSquare318.into R c L hz)
    (fun i => inferInstance) _ (ContactNormalizedZeroCartierSquare318.square R c L hz)
    (ContactNormalizedCartierTest318.regular_charts R c L hz)
  intro x
  exact RelativeAmbientCharts318.covers
    (ContactRelativeStructuralHOne318.projection R c)
    (ContactNormalizedSectionParameter318.projection R c L hz)
    (ContactNormalizedSectionParameter318.cover R c L hz)
    (fun i => curve (ContactNormalizedCartierTest318.ring R c L hz i) c)
    (fun i => ContactRelativeCoefficientChange318.curveMap R
      (ContactNormalizedCartierTest318.ring R c L hz i)
      ((ContactNormalizedCartierTest318.coefficient R c L hz i).comp
        (ContactOriginalSectionParameter318.parameterCoefficient R c L)) c)
    (fun i => ContactRelativeStructuralHOne318.projection
      (ContactNormalizedCartierTest318.ring R c L hz i) c)
    (ContactNormalizedAmbientCharts318.coefficient_square R c L hz) x

/-- Genuine global effective-Cartier chart criterion on the actual
closed finite-flat normalized zero family. This is still a fixed-line
linear system, not represented Picard or a numerical degree assertion. -/
theorem closed_and_regular_charts :
    IsClosedImmersion (ContactNormalizedGlobalClosedFamily318.into R c L hz) ∧
    OriginalRegularClosedCharts318.Property (ContactNormalizedGlobalClosedFamily318.into R c L hz) :=
  ⟨inferInstance,regular_charts R c L hz⟩
end ContactNormalizedGlobalCartier318
