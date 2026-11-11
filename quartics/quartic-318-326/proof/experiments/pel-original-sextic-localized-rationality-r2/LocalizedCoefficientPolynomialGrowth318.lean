module
public import LocalizedAnalyticPolynomialNumerator318
public import LocalizedPolynomialEvaluationSeparation318
public section
noncomputable section
namespace LocalizedCoefficientPolynomialGrowth318
open ComplexPolynomialOpenPoints318 LocalizedComplexCoefficientAnalytic318

/-- A genuine localized coefficient with a denominator-FREE growth bound
is an element of the original polynomial ring. Analyticity is supplied by
its actual rational expression; no extension across the divisor is assumed. -/
theorem exists_polynomial (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (a : Localization.Away d) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      ‖evaluation d v hv a‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away d) P = a := by
  obtain ⟨P,hP⟩ := BivariateRationalNumerator318.exists_numerator d hd
    (value d a) 0 N C hC (fun v hv => analyticAt_value d a v hv)
    (fun v hv => by simpa only [pow_zero,one_mul,value_on_open d a v hv] using hb v hv)
  refine ⟨P,LocalizedPolynomialEvaluationSeparation318.ext d hd _ _ ?_⟩
  intro v hv
  rw [evaluation_source]
  simpa only [pow_zero,one_mul,value_on_open d a v hv] using hP v hv
end LocalizedCoefficientPolynomialGrowth318
