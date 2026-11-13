module
public import ContactProjectiveFiniteProjective318
public import ContactProjectiveIdealAbel318
public section
noncomputable section
namespace ContactProjectiveDegreeData318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
/-- Intrinsic effective finite-flat Cartier data on the original projective
source, with regularity on the full closed map and properties on the
WHOLE projection. This does not yet represent the moduli functor. -/
structure EffectiveDatum where
  datum : Datum R c
  regular : OriginalRegularClosedCharts318.Property (into R c datum)
  finite : IsFinite (projection R c datum)
  flat : Flat (projection R c datum)
attribute [instance] EffectiveDatum.finite EffectiveDatum.flat
variable (D : EffectiveDatum R c)
instance finitePresentation : LocallyOfFinitePresentation (projection R c D.datum) := by
  letI := RegularClosedFinitePresentation318.finitePresentation (into R c D.datum) D.regular
  change LocallyOfFinitePresentation (into R c D.datum ≫ ContactRelativeStructuralHOne318.projection R c)
  infer_instance
@[expose] def degree : PrimeSpectrum R → ℕ := FiniteFlatRankBounds318.degree R (projection R c D.datum)
lemma locallyConstant : IsLocallyConstant (degree R c D) := FiniteFlatRankBounds318.locallyConstant R _
lemma bounded : ∃ N : ℕ, ∀ x, degree R c D x≤N := FiniteFlatRankBounds318.exists_bound R _
/-- Constant degree is imposed on every coefficient prime, rather than
confusing a globally selected frame size with the true fiber rank. -/
@[expose] def FixedDegree (n : ℕ) := {D : EffectiveDatum R c // ∀ x,degree R c D x=n}
@[expose] def BoundedDegree (N : ℕ) := {D : EffectiveDatum R c // ∀ x,degree R c D x≤N}
lemma exists_bounded : ∃ N : ℕ, ∃ E : BoundedDegree R c N, E.val=D := by
  obtain ⟨N,hN⟩ := bounded R c D
  exact ⟨N,⟨D,hN⟩,rfl⟩
end ContactProjectiveDegreeData318
