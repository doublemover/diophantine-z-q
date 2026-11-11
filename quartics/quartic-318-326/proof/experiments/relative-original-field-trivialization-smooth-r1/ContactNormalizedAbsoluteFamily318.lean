module
public import ContactNormalizedAbsoluteAmbient318
public section
noncomputable section
namespace ContactNormalizedAbsoluteFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "a" => ContactNormalizedAbsoluteAmbient318.base R c L hz
local notation "q" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "e" => ContactNormalizedAbsoluteAmbient318.comparison R c L hz
@[expose] def into : ContactNormalizedGlobalZero318.scheme R c L hz ⟶ pullback p a := q ≫ e.hom
instance closed : IsClosedImmersion (into R c L hz) := inferInstance
@[reassoc] lemma projection : into R c L hz ≫ pullback.snd p a=ContactNormalizedZeroProjection318.projection R c L hz := by
  rw [into,Category.assoc,ContactNormalizedAbsoluteAmbient318.base_projection,
    ContactNormalizedGlobalClosedFamily318.into_projection]
instance finite : IsFinite (into R c L hz ≫ pullback.snd p a) := by rw [projection]; infer_instance
instance flat : Flat (into R c L hz ≫ pullback.snd p a) := by rw [projection]; infer_instance
instance presentation : LocallyOfFinitePresentation (into R c L hz ≫ pullback.snd p a) := by rw [projection]; infer_instance
/-- The original complete regular quotient charts survive the exact
ambient comparison, with no change in the actual normalized divisor. -/
lemma regular : OriginalRegularClosedCharts318.Property (into R c L hz) :=
  RegularClosedSquareIso318.transport q (into R c L hz) (Iso.refl _) e
    (by simp only [Iso.refl_hom,Category.id_comp]; rfl)
    (ContactNormalizedGlobalCartier318.regular_charts R c L hz)
end ContactNormalizedAbsoluteFamily318
