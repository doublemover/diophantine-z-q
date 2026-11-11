module
public import ContactProjectiveQuotientCartier318
public import RegularClosedFinitePresentation318
public import FiniteFlatRankBounds318
public section
noncomputable section
namespace ContactProjectiveFiniteProjective318
open AlgebraicGeometry CategoryTheory
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
  (hf : OriginalRegularIdealCover318.Property (CommRingCat.of (finiteRing R c)) D.finiteIdeal)
  (hi : OriginalRegularIdealCover318.Property (CommRingCat.of (infinityRing R c)) D.infinityIdeal)
lemma immersion_finitePresentation : LocallyOfFinitePresentation (into R c D) :=
  RegularClosedFinitePresentation318.finitePresentation (into R c D)
    (ContactProjectiveQuotientCartier318.regular_charts R c D hf hi)
lemma projection_finitePresentation : LocallyOfFinitePresentation (projection R c D) := by
  letI := immersion_finitePresentation R c D hf hi
  change LocallyOfFinitePresentation (into R c D ≫ ContactRelativeStructuralHOne318.projection R c)
  infer_instance
variable [IsFinite (projection R c D)] [Flat (projection R c D)]
/-- Actual finite projectivity of functions on the WHOLE projective
quotient: finite presentation is supplied by its true Cartier charts,
not silently inferred from finite flatness over arbitrary rings. -/
lemma finite_projective : Module.Finite R (FiniteAffineAlgebra318.ring R (projection R c D)) ∧
    Module.Projective R (FiniteAffineAlgebra318.ring R (projection R c D)) := by
  letI := projection_finitePresentation R c D hf hi
  exact ⟨inferInstance,inferInstance⟩
lemma bounded_degree : ∃ N : ℕ, ∀ x : PrimeSpectrum R,
    Module.rankAtStalk (FiniteAffineAlgebra318.ring R (projection R c D)) x≤N := by
  letI := projection_finitePresentation R c D hf hi
  exact FiniteFlatRankBounds318.exists_bound R (projection R c D)
end ContactProjectiveFiniteProjective318
