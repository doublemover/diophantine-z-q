module
public import ThreeProjectiveJCertificates318
public import ActualThreeExceptionalParameter318
public section
noncomputable section
namespace ActualThreeJChartConsumer318
open Polynomial ThreeProjectiveJCertificates318 ActualThreeExceptionalParameter318
open GammaOneFiber318 PeterssonQuotient318

/-- Both numerator and denominator are evaluations of the actual rational
polynomials reserved for the finite source chart of the projective j map. -/
lemma finite_evaluation (t : ℂ) :
    aeval t finiteNumerator = homogeneousNumerator t 1 ∧
      aeval t finiteDenominator = homogeneousDenominator t 1 := by
  simp [finiteNumerator,finiteDenominator,homogeneousNumerator,homogeneousDenominator,map_ofNat]

lemma reciprocal_evaluation (s : ℂ) :
    aeval s reciprocalNumerator = homogeneousNumerator 1 s ∧
      aeval s reciprocalDenominator = homogeneousDenominator 1 s := by
  simp [reciprocalNumerator,reciprocalDenominator,homogeneousNumerator,homogeneousDenominator,map_ofNat]

/-- Exact finite-chart identity for the original rational j formula. -/
theorem finite_J (t : ℂ) :
    ThreeCompactParameter318.J t = aeval t finiteNumerator / aeval t finiteDenominator := by
  rw [(finite_evaluation t).1,(finite_evaluation t).2]
  simp only [ThreeCompactParameter318.J,homogeneousNumerator,homogeneousDenominator,mul_one]

/-- The reciprocal chart represents the same rational function on the exact
overlap. Nonvanishing of t is explicit, including in every cancellation. -/
theorem reciprocal_J (t : ℂ) (ht : t ≠ 0) :
    ThreeCompactParameter318.J t =
      aeval t⁻¹ reciprocalNumerator / aeval t⁻¹ reciprocalDenominator := by
  rw [(reciprocal_evaluation t⁻¹).1,(reciprocal_evaluation t⁻¹).2]
  unfold ThreeCompactParameter318.J homogeneousNumerator homogeneousDenominator
  field_simp [ht] <;> ring

/-- The finite polynomial pair consumes the original modular j identity at
every original quotient point, not only the old admissible generic locus. -/
theorem original_j_finite (b : Base (image 3)) :
    QuotientJ318.jMap 3 b =
      aeval (quotientParameter b) finiteNumerator /
        aeval (quotientParameter b) finiteDenominator := by
  rw [←quotientParameter_j]
  exact finite_J _

theorem original_finite_denominator_ne_zero (b : Base (image 3)) :
    aeval (quotientParameter b) finiteDenominator ≠ 0 := by
  rw [(finite_evaluation _).2]
  simpa only [homogeneousDenominator,mul_one] using
    pow_ne_zero 3 (quotientParameter_ne_zero b)

/-- The same original modular j map in the other source chart. -/
theorem original_j_reciprocal (b : Base (image 3)) :
    QuotientJ318.jMap 3 b =
      aeval (quotientParameter b)⁻¹ reciprocalNumerator /
        aeval (quotientParameter b)⁻¹ reciprocalDenominator := by
  rw [←quotientParameter_j]
  exact reciprocal_J _ (quotientParameter_ne_zero b)

/-- The two boundary source origins have nonzero numerator and zero
denominator. This fixes their target chart choice, not yet an order of pole
or a global morphism of schemes. -/
theorem boundary_chart_values :
    aeval (0:ℂ) finiteNumerator = 3^18 ∧
      aeval (0:ℂ) finiteDenominator = 0 ∧
      aeval (0:ℂ) reciprocalNumerator = 1 ∧
      aeval (0:ℂ) reciprocalDenominator = 0 := by
  norm_num [finiteNumerator,finiteDenominator,reciprocalNumerator,reciprocalDenominator,map_ofNat]

end ActualThreeJChartConsumer318
