module
public import ContactNormalizedZeroCartesian318
public section
noncomputable section
namespace ContactNormalizedGlobalFiniteFlat318
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
local notation "π" => ContactNormalizedZeroProjection318.projection R c L hz

private lemma inverse_projection (i : Fin F.size) :
    (ContactNormalizedZeroCartesian318.square R c L hz i).isoPullback.inv ≫ p i=
      pullback.snd π (u i) :=
  (ContactNormalizedZeroCartesian318.square R c L hz i).isoPullback_inv_snd

/-- Finiteness descends from the SAME original normalized zero charts
through their actual Cartesian squares over the full parameter cover. -/
instance finite : IsFinite π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@IsFinite)
    (ContactNormalizedSectionParameter318.cover R c L hz)
  intro i
  change IsFinite (pullback.snd π (u i))
  rw [← inverse_projection R c L hz i]
  infer_instance
instance flat : Flat π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@Flat)
    (ContactNormalizedSectionParameter318.cover R c L hz)
  intro i
  change Flat (pullback.snd π (u i))
  rw [← inverse_projection R c L hz i]
  infer_instance
instance finitePresentation : LocallyOfFinitePresentation π := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@LocallyOfFinitePresentation)
    (ContactNormalizedSectionParameter318.cover R c L hz)
  intro i
  change LocallyOfFinitePresentation (pullback.snd π (u i))
  rw [← inverse_projection R c L hz i]
  infer_instance

/-- A genuine GLOBAL finite-flat finitely presented family over the
actual normalized original-section parameter. Numerical degree, the
universal property for varying line classes, and represented Picard
remain separate statements; none is included as an assumed input here. -/
theorem properties : IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π :=
  ⟨inferInstance,inferInstance,inferInstance⟩
end ContactNormalizedGlobalFiniteFlat318
