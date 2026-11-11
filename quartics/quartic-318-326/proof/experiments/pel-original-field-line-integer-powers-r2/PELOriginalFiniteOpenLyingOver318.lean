module
public import PELOriginalFiniteOpenBaseChange318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section
namespace PELOriginalFiniteOpenLyingOver318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalProjectedChartIndependence318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

lemma polynomial_injective (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    Function.Injective (polynomialMap τ hτ j x) :=
  (algebraicIndependent_iff_injective_aeval.mp (independent τ hτ x j hx))

/-- Faithfulness is preserved under the literal base localization;
no source component or coordinate quotient has been selected. -/
theorem localized_injective (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) (p : BasePolynomial) :
    Function.Injective (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p) := by
  apply Localization.awayMap_injective_iff.mpr
  intro a ha
  have ha0 : a = 0 := polynomial_injective τ hτ j x hx (ha.trans (map_zero _).symm)
  exact ⟨0,by simp only [ha0,mul_zero]⟩

/-- Every base prime of the produced finite open has a genuine source
prime. This is actual integral lying-over, NOT surjectivity of the
original analytic source onto the algebraic candidate. -/
theorem finite_open_surjective (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) (p : BasePolynomial)
    (hf : (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p).Finite) :
    Surjective (localizedProjection τ hτ j x p) := by
  have hi := (RingHom.finite_iff_isIntegral_and_finiteType.mp hf).1
  exact ⟨hi.comap_surjective (localized_injective τ hτ j x hx p)⟩

/-- A faithful finite surjective projected chart over a produced
nonzero literal polynomial open, retaining an actual original point. -/
theorem produced_finite_surjective_open (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ p : BasePolynomial, p ≠ 0 ∧
      IsFinite (localizedProjection τ hτ j x p) ∧
      Surjective (localizedProjection τ hτ j x p) ∧
      IsOpenImmersion (localizedChart τ hτ j x p) ∧
      ∃ z : ComplexVectors, ∃ hz : value τ hτ 3 j z ≠ 0,
        PELOriginalChartAnalyticEvaluation318.algebraEvaluation τ hτ z j hz
          (polynomialMap τ hτ j x p) ≠ 0 := by
  obtain ⟨p,hp,hf⟩ := exists_polynomial_finite_open τ hτ j x hx
  exact ⟨p,hp,(IsFinite.SpecMap_iff _).mpr hf,
    finite_open_surjective τ hτ j x hx p hf,
    PELOriginalFiniteOpenBaseChange318.actual_open_immersion τ hτ j x p,
    PELOriginalFiniteOpenAnalyticMeeting318.meets_original_patch τ hτ j x hx p hp⟩
end PELOriginalFiniteOpenLyingOver318
