module
public import LocalizedCoefficientPolynomialGrowth318
public import Mathlib.Algebra.Polynomial.BigOperators
public section
noncomputable section
namespace LocalizedMonicPolynomialDescent318
open Polynomial ComplexPolynomialOpenPoints318
abbrev Base := MvPolynomial (Fin 2) ℂ

/-- A whole localized polynomial whose coefficients have genuine
polynomial growth without poles descends coefficientwise to the SAME
base ring. Each coefficient may have its own bound. -/
theorem exists_polynomial (d : Base) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d))
    (hb : ∀ n, ∃ N C, 0 ≤ C ∧ ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      ‖evaluation d v hv (Q.coeff n)‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : Polynomial Base, P.map (algebraMap Base (Localization.Away d)) = Q := by
  classical
  have hc (n : ℕ) : ∃ a : Base,
      algebraMap Base (Localization.Away d) a = Q.coeff n := by
    obtain ⟨N,C,hC,hb⟩ := hb n
    exact LocalizedCoefficientPolynomialGrowth318.exists_polynomial d hd (Q.coeff n) N C hC hb
  choose a ha using hc
  let P : Polynomial Base := ∑ n ∈ Finset.range (Q.natDegree+1), monomial n (a n)
  refine ⟨P,?_⟩
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  by_cases hn : n < Q.natDegree+1
  · have h : P.coeff n = a n := by
      simp [P,Polynomial.coeff_sum,Polynomial.coeff_monomial,hn]
    rw [h,ha]
  · have h : P.coeff n = 0 := by
      simp [P,Polynomial.coeff_sum,Polynomial.coeff_monomial,hn]
    rw [h,map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Descent preserves genuine monicity, not merely specialized monicity
at a selected set of points. The original localization map is injective. -/
theorem exists_monic (d : Base) (hd : d ≠ 0)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (hb : ∀ n, ∃ N C, 0 ≤ C ∧ ∀ v (hv : MvPolynomial.eval v d ≠ 0),
      ‖evaluation d v hv (Q.coeff n)‖ ≤ C * (1+‖v‖)^N) :
    ∃ P : Polynomial Base, P.Monic ∧
      P.map (algebraMap Base (Localization.Away d)) = Q := by
  obtain ⟨P,hP⟩ := exists_polynomial d hd Q hb
  have hi : Function.Injective (algebraMap Base (Localization.Away d)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  refine ⟨P,Polynomial.monic_of_injective hi ?_,hP⟩
  rw [hP]
  exact hm
end LocalizedMonicPolynomialDescent318
