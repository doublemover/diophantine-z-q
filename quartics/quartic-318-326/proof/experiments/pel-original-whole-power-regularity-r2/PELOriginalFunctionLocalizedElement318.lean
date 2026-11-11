module
public import PELOriginalFunctionLocalizedPolynomial318
public section
noncomputable section
namespace PELOriginalFunctionLocalizedElement318
open Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalProjectedChartIndependence318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalOpenPrimitiveSheets318
open PELOriginalFunctionRootInterpolation318 PELOriginalSectionMultiplication318
open PELOriginalLocalizedEvaluationSquare318 PELOriginalPrimitiveLocalReconstruction318
open PELOriginalPolynomialGrowthFunction318
open PELOriginalPolynomialGrowthFunction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- The actual original function is an element of the WHOLE original chart
localized at the same produced denominator. Evaluation agrees at every
independent root and every original point in that entire open. -/
theorem exists_element (hd : d ≠ 0) (hm : Q.Monic) (hs : Q.Separable)
    (F : Data τ hτ j)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    ∃ a : Localization.Away (polynomialMap τ hτ j x d),
      (∀ q : OpenRoots d Q, (rootPoint τ hτ j x d Q e he q).val a =
        rootValue τ hτ j x d Q e he F q) ∧
      ∀ z : originalDomain τ hτ j x d,
        (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val a =
          F.onCover z.val := by
  obtain ⟨H,hdeg,hH,hHz⟩ := PELOriginalFunctionLocalizedPolynomial318.exists_polynomial
    τ hτ j x d Q e he hd hm hs F honto
  refine ⟨e (AdjoinRoot.mk Q H),?_,?_⟩
  · intro q
    rw [MonogenicOriginalCoordinates318.evaluate_representative
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) Q e he]
    have hr : (rootPoint τ hτ j x d Q e he q).val (e (AdjoinRoot.root Q)) = q.val.val.2 :=
      candidatePoint_root τ hτ j x d Q e he _ q.property _ _
    rw [hr,←Polynomial.eval_map,hH]
    exact LocalizedRootInterpolation318.evaluation d Q hm (rootValue τ hτ j x d Q e he F) q
  · intro z
    rw [MonogenicOriginalCoordinates318.evaluate_representative
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom d) Q e he,
      ←primitiveValue_eq τ hτ j x d Q e z.val z.property.1 z.property.2]
    exact hHz z

/-- An explicit original chart numerator and a power of the same chart
denominator represent the actual original function on the full open.
This is genuine chart-ring rationality, not algebraicity in a larger
section field or an expression on only one analytic sheet. -/
theorem exists_chart_fraction (hd : d ≠ 0) (hm : Q.Monic) (hs : Q.Separable)
    (F : Data τ hτ j)
    (honto : Function.Surjective (originalOpenRootPoint τ hτ j x d Q e he)) :
    ∃ a : CoordinateChart τ hτ j, ∃ n : ℕ,
      ∀ z : originalDomain τ hτ j x d,
        F.onCover z.val =
          algebraEvaluation τ hτ z.val j z.property.1 a /
            (MvPolynomial.eval (projectedVector τ hτ j x z.val) d)^n := by
  obtain ⟨a,ha,hz⟩ := exists_element τ hτ j x d Q e he hd hm hs F honto
  obtain ⟨⟨b,m,hm⟩,heq⟩ := IsLocalization.surj
    (Submonoid.powers (polynomialMap τ hτ j x d)) a
  obtain ⟨n,hn⟩ := hm
  refine ⟨b,n,?_⟩
  intro z
  have h := congrArg (originalPoint τ hτ j x z.val z.property.1 d z.property.2).val heq
  rw [map_mul,originalPoint_source,originalPoint_source,←hn,map_pow,
    polynomial_evaluation,hz z] at h
  exact (eq_div_iff (pow_ne_zero n z.property.2)).mpr h
/-- A SINGLE produced nonempty algebraic chart open works for EVERY
function satisfying the explicit original differentiability and growth inputs.
No monogenic model, full-fiber surjectivity or rationality premise is supplied. -/
theorem exists_common_open (hx : value τ hτ 3 j x ≠ 0) :
    ∃ d : BasePolynomial, d ≠ 0 ∧ polynomialMap τ hτ j x d ≠ 0 ∧
      ∀ F : Data τ hτ j, ∃ a : CoordinateChart τ hτ j, ∃ n : ℕ,
        ∀ z : originalDomain τ hτ j x d,
          F.onCover z.val =
            algebraEvaluation τ hτ z.val j z.property.1 a /
              (MvPolynomial.eval (projectedVector τ hτ j x z.val) d)^n := by
  obtain ⟨d,hd,ha,Q,β,hQ,hm,hs,hβ,e,heβ,he,honto⟩ :=
    PELOriginalFullPrimitiveOpen318.exists_full_original_open τ hτ j x hx
  exact ⟨d,hd,ha,fun F => exists_chart_fraction τ hτ j x d Q e he hd hm hs F honto⟩
end PELOriginalFunctionLocalizedElement318
