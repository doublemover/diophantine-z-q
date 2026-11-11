module
public import LocalizedAnalyticPolynomialNumerator318
public import LocalizedPolynomialEvaluationSeparation318
public import Mathlib.Algebra.Polynomial.BigOperators
public section
noncomputable section
namespace LocalizedAnalyticPolynomialFamily318
open Polynomial ComplexPolynomialOpenPoints318

/-- A finite-degree polynomial-valued analytic family with genuine
uniform coefficient pole growth is a single polynomial over the SAME
whole localization. The construction uses every coefficient through the
fixed degree bound, not a chosen local factor or a constant-degree premise. -/
theorem exists_polynomial (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (F : (Fin 2 → ℂ) → Polynomial ℂ) (K M N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hdeg : ∀ v, MvPolynomial.eval v d ≠ 0 → (F v).natDegree ≤ K)
    (hf : ∀ n v, MvPolynomial.eval v d ≠ 0 → AnalyticAt ℂ (fun w => (F w).coeff n) v)
    (hb : ∀ n v, MvPolynomial.eval v d ≠ 0 →
      ‖MvPolynomial.eval v d ^ M * (F v).coeff n‖ ≤ C*(1+‖v‖)^N) :
    ∃ H : Polynomial (Localization.Away d), H.natDegree ≤ K ∧
      ∀ v (hv : MvPolynomial.eval v d ≠ 0), H.map (evaluation d v hv) = F v := by
  classical
  have hc (n : ℕ) : ∃ a : Localization.Away d,
      ∀ v (hv : MvPolynomial.eval v d ≠ 0), evaluation d v hv a = (F v).coeff n := by
    obtain ⟨P,a,ha,he⟩ := LocalizedAnalyticPolynomialNumerator318.exists_localized_element
      d hd (fun v => (F v).coeff n) M N C hC (hf n) (hb n)
    exact ⟨a,he⟩
  choose a ha using hc
  let H : Polynomial (Localization.Away d) := ∑ n ∈ Finset.range (K+1), monomial n (a n)
  refine ⟨H,?_,?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  · intro v hv
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_map]
    by_cases hn : n < K+1
    · have he : H.coeff n = a n := by
        simp [H,Polynomial.coeff_sum,Polynomial.coeff_monomial,hn]
      rw [he,ha n v hv]
    · have he : H.coeff n = 0 := by
        simp [H,Polynomial.coeff_sum,Polynomial.coeff_monomial,hn]
      rw [he,map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt
        ((hdeg v hv).trans_lt (by omega))).symm
end LocalizedAnalyticPolynomialFamily318
