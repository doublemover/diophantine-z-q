module
public import ContactNormalizedGlobalZero318
public section
noncomputable section
namespace ContactNormalizedZeroProjection318
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

/-- The original zero charts descend to an ACTUAL morphism from the
global zero scheme to the ACTUAL glued normalized-section parameter. -/
@[expose] def projection : ContactNormalizedGlobalZero318.scheme R c L hz ⟶
    ContactNormalizedSectionParameter318.scheme R c L hz := by
  fapply Multicoequalizer.desc
  · exact fun i => p i ≫ u i
  rintro ⟨i,j⟩
  change inc i j ≫ (p i ≫ u i)=((t i j).hom ≫ inc j i) ≫ (p j ≫ u j)
  rw [Category.assoc,ContactNormalizedZeroTransitions318.transition_chart_projection_assoc,
    ProjectiveParameterSliceGluing318.glue_condition]
  change inc i j ≫ (p i ≫ u i)=proj i j ≫
    (ProjectiveParameterSliceSchemes318.inclusion R P i j ≫ u i)
  rw [← Category.assoc,← Category.assoc,pullback.condition]
@[reassoc] lemma into_projection (i : Fin F.size) :
    ContactNormalizedGlobalZero318.into R c L hz i ≫ projection R c L hz=p i ≫ u i :=
  Multicoequalizer.π_desc _ _ _ _ _
end ContactNormalizedZeroProjection318
