module
public import ContactFieldArbitrarySectionSmooth318
public import ContactTrivializationLocallyFinitePresentation318
public section
noncomputable section
namespace ContactFieldTrivializationSmooth318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
  (L : Line (curve (CommRingCat.of K) c))
local notation "R" => CommRingCat.of K

/-- The SAME original open classifying full trivializations of a line
fixed over a field is genuinely smooth, even with nonzero H1. It may be
empty; this does not assert a trivialization or a smooth arbitrary-line
Picard fiber over a varying coefficient base. -/
instance smooth : Smooth (ContactTrivializationLocallyFinitePresentation318.projection R c L) := by
  unfold ContactTrivializationLocallyFinitePresentation318.projection
  infer_instance

instance baseChange {T : Scheme.{0}} (f : T ⟶ Spec R) :
    Smooth (pullback.snd (ContactTrivializationLocallyFinitePresentation318.projection R c L) f) :=
  inferInstance
end ContactFieldTrivializationSmooth318
