module
public import BivariateRationalNumerator318
public import LocalizedComplexCoefficientAnalytic318
public section
noncomputable section
namespace LocalizedAnalyticPolynomialNumerator318
open ComplexPolynomialOpenPoints318

lemma evaluation_invSelf (d : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ)
    (hv : MvPolynomial.eval v d ≠ 0) :
    evaluation d v hv (IsLocalization.Away.invSelf d : Localization.Away d) =
      (MvPolynomial.eval v d)⁻¹ := by
  have h := congrArg (evaluation d v hv)
    (IsLocalization.Away.mul_invSelf d (S := Localization.Away d))
  rw [map_mul,evaluation_source,map_one] at h
  apply mul_left_cancel₀ hv
  rw [h,mul_inv_cancel₀ hv]

/-- The polynomial numerator realizes the original analytic function as
an element of the WHOLE specified localization. The same d and exponent
M are retained, and every actual localization evaluation agrees on D(d). -/
theorem exists_localized_element (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (f : (Fin 2 → ℂ) → ℂ) (M N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ v, MvPolynomial.eval v d ≠ 0 → AnalyticAt ℂ f v)
    (hb : ∀ v, MvPolynomial.eval v d ≠ 0 →
      ‖MvPolynomial.eval v d ^ M * f v‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∃ a : Localization.Away d,
      a = algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away d) P *
        (IsLocalization.Away.invSelf d)^M ∧
      ∀ v (hv : MvPolynomial.eval v d ≠ 0), evaluation d v hv a = f v := by
  obtain ⟨P,hP⟩ := BivariateRationalNumerator318.exists_rational_formula d hd f M N C hC hf hb
  refine ⟨P,algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away d) P *
    (IsLocalization.Away.invSelf d)^M,rfl,?_⟩
  intro v hv
  rw [map_mul,evaluation_source,map_pow,evaluation_invSelf,←inv_pow,←div_eq_mul_inv]
  exact (hP v hv).symm
end LocalizedAnalyticPolynomialNumerator318
