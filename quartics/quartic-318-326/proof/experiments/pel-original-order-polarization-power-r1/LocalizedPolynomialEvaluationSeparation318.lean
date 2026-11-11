module
public import ComplexPolynomialOpenPoints318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace LocalizedPolynomialEvaluationSeparation318
open ComplexPolynomialOpenPoints318
variable {ι : Type*}

/-- Evaluations at ALL points of the actual principal open separate the
whole localization, not only its polynomial subring. The numerator times
d vanishes even at points outside D(d), so ordinary polynomial funext
suffices; no density of a selected image is assumed. -/
theorem eq_zero (d : MvPolynomial ι ℂ) (hd : d ≠ 0) (a : Localization.Away d)
    (ha : ∀ v (hv : MvPolynomial.eval v d ≠ 0), evaluation d v hv a = 0) : a = 0 := by
  obtain ⟨⟨b,s⟩,he⟩ := IsLocalization.surj (Submonoid.powers d) a
  have hb : b*d = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul,map_zero]
    by_cases hv : MvPolynomial.eval v d = 0
    · rw [hv,mul_zero]
    · have hh := congrArg (evaluation d v hv) he
      rw [map_mul,evaluation_source,evaluation_source,ha v hv,zero_mul] at hh
      rw [←hh,zero_mul]
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hd
  rw [hb0,map_zero] at he
  obtain ⟨u,hu⟩ := IsLocalization.map_units (Localization.Away d) s
  rw [←hu] at he
  have hh := congrArg (fun z : Localization.Away d => z * (u⁻¹).val) he
  simpa only [mul_assoc,Units.mul_inv,mul_one,zero_mul] using hh

/-- Whole localized coefficients are equal exactly when their actual
complex evaluations agree at every point of the original base open. -/
theorem ext (d : MvPolynomial ι ℂ) (hd : d ≠ 0) (a b : Localization.Away d)
    (h : ∀ v (hv : MvPolynomial.eval v d ≠ 0), evaluation d v hv a = evaluation d v hv b) :
    a = b := by
  apply sub_eq_zero.mp
  apply eq_zero d hd
  intro v hv
  rw [map_sub,h v hv,sub_self]

/-- Polynomial identities over the whole localization can be checked
by the SAME coefficient evaluations on all of D(d). -/
theorem polynomial_ext (d : MvPolynomial ι ℂ) (hd : d ≠ 0)
    (P Q : Polynomial (Localization.Away d))
    (h : ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      P.map (evaluation d v hv) = Q.map (evaluation d v hv)) : P = Q := by
  apply Polynomial.ext
  intro n
  apply ext d hd
  intro v hv
  have hh := congrArg (fun p : Polynomial ℂ => p.coeff n) (h v hv)
  simpa only [Polynomial.coeff_map] using hh
end LocalizedPolynomialEvaluationSeparation318
