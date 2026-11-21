module
public import Mathlib.Tactic
public section
namespace ActualA4ShortProduct318

/-- Four integer residue-hit counts are each within one of u. For
u≥1, the exact first-order loss is at most 15u³. The proof is a
four-term signed telescope, not a leading-degree heuristic. -/
theorem product_error (u a b c d : ℝ) (hu : 1 ≤ u)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ea : |a-u| ≤ 1) (eb : |b-u| ≤ 1) (ec : |c-u| ≤ 1) (ed : |d-u| ≤ 1) :
    |a*b*c*d-u^4| ≤ 15*u^3 := by
  have hU : 0 ≤ u := zero_le_one.trans hu
  have hB : b ≤ 2*u := by linarith only [(abs_le.mp eb).2,hu]
  have hC : c ≤ 2*u := by linarith only [(abs_le.mp ec).2,hu]
  have hD : d ≤ 2*u := by linarith only [(abs_le.mp ed).2,hu]
  have e₁ : |(a-u)*b*c*d| ≤ 8*u^3 := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hb,abs_of_nonneg hc,abs_of_nonneg hd]
    calc
      _ ≤ 1*(2*u)*(2*u)*(2*u) := by gcongr
      _ = _ := by ring
  have e₂ : |u*(b-u)*c*d| ≤ 4*u^3 := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hU,abs_of_nonneg hc,abs_of_nonneg hd]
    calc
      _ ≤ u*1*(2*u)*(2*u) := by gcongr
      _ = _ := by ring
  have e₃ : |u^2*(c-u)*d| ≤ 2*u^3 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg u),abs_of_nonneg hd]
    calc
      _ ≤ u^2*1*(2*u) := by gcongr
      _ = _ := by ring
  have e₄ : |u^3*(d-u)| ≤ u^3 := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg hU _)]
    exact (mul_le_mul_of_nonneg_left ed (pow_nonneg hU 3)).trans_eq (mul_one _)
  rw [show a*b*c*d-u^4=(a-u)*b*c*d+u*(b-u)*c*d+u^2*(c-u)*d+u^3*(d-u) by ring]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (|(a-u)*b*c*d+u*(b-u)*c*d|+|u^2*(c-u)*d|)+|u^3*(d-u)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((|(a-u)*b*c*d|+|u*(b-u)*c*d|)+|u^2*(c-u)*d|)+|u^3*(d-u)| := by
      exact add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ _ := by linarith only [e₁,e₂,e₃,e₄]

end ActualA4ShortProduct318
