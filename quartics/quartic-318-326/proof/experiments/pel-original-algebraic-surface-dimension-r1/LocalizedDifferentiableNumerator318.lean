module
public import DifferentiableRationalNumerator318
public import LocalizedAnalyticPolynomialNumerator318
public import LocalizedComplexCoefficientAnalytic318
public section
noncomputable section
namespace LocalizedDifferentiableNumerator318
open ComplexPolynomialOpenPoints318

/-- The polynomial numerator realizes the original complex differentiable function as
an element of the WHOLE specified localization. The same d and exponent
M are retained, and every actual localization evaluation agrees on D(d). -/
theorem exists_localized_element (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (f : (Fin 2 → ℂ) → ℂ) (M N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ v, MvPolynomial.eval v d ≠ 0 → DifferentiableAt ℂ f v)
    (hb : ∀ v, MvPolynomial.eval v d ≠ 0 →
      ‖MvPolynomial.eval v d ^ M * f v‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∃ a : Localization.Away d,
      a = algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away d) P *
        (IsLocalization.Away.invSelf d)^M ∧
      ∀ v (hv : MvPolynomial.eval v d ≠ 0), evaluation d v hv a = f v := by
  obtain ⟨P,hP⟩ := DifferentiableRationalNumerator318.exists_rational_formula d hd f M N C hC hf hb
  refine ⟨P,algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away d) P *
    (IsLocalization.Away.invSelf d)^M,rfl,?_⟩
  intro v hv
  rw [map_mul,evaluation_source,map_pow,LocalizedAnalyticPolynomialNumerator318.evaluation_invSelf,←inv_pow,←div_eq_mul_inv]
  exact (hP v hv).symm
end LocalizedDifferentiableNumerator318
