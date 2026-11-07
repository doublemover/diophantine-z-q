module
public import LiteralMetricExtension318
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public section
noncomputable section
namespace BicanonicalCharts318
open MetricSmoothExtension318 MetricPullback318 LiteralMetricExtension318
open scoped BigOperators Topology
set_option maxHeartbeats 0

@[expose] def contactPolynomial (a : Fin 4 → ℂ) (t : ℂ) : ℂ := ∏ j, (t - a j)
@[expose] def q0 (a : Fin 4 → ℂ) (t : ℂ) : ℂ := 1 / contactPolynomial a t
@[expose] def q1 (a : Fin 4 → ℂ) (t : ℂ) : ℂ := t * q0 a t
@[expose] def branchDen (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) : ℂ :=
  ∏ j : {j : Fin 4 // j ≠ i}, (a i - a j + z^2)
@[expose] def branchQ0 (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) : ℂ := 4 / branchDen a i z
@[expose] def branchQ1 (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) : ℂ :=
  (a i + z^2) * branchQ0 a i z
@[expose] def infinityDen (a : Fin 4 → ℂ) (z : ℂ) : ℂ := ∏ j, (1 - a j * z^2)
@[expose] def infinityQ0 (a : Fin 4 → ℂ) (z : ℂ) : ℂ := 4*z^2 / infinityDen a z
@[expose] def infinityQ1 (a : Fin 4 → ℂ) (z : ℂ) : ℂ := 4 / infinityDen a z

theorem finite_polynomial_pullback (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) :
    contactPolynomial a (a i + z^2) = z^2 * branchDen a i z := by
  classical
  unfold contactPolynomial branchDen
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [add_sub_cancel_left]
  rw [mul_comm]
  congr 1
  simp_rw [show ∀ j : Fin 4, a i + z^2 - a j = a i - a j + z^2 by intro j; ring]
  exact Finset.prod_subtype (Finset.univ.erase i) (by simp) _

theorem infinity_polynomial_pullback (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    contactPolynomial a (1 / z^2) = infinityDen a z / (z^2)^4 := by
  unfold contactPolynomial infinityDen
  have he (j : Fin 4) : (1 : ℂ) / z^2 - a j = (1 - a j*z^2) / z^2 := by field_simp
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp

theorem finite_q0_pullback (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) (hz : z ≠ 0) :
    q0 a (a i + z^2) * (deriv (fun w : ℂ => a i + w^2) z)^2 = branchQ0 a i z := by
  rw [branch_map_derivative]
  unfold q0 branchQ0
  rw [finite_polynomial_pullback]
  by_cases hd : branchDen a i z = 0
  · simp [hd]
  · field_simp
    ring

theorem finite_q1_pullback (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) (hz : z ≠ 0) :
    q1 a (a i + z^2) * (deriv (fun w : ℂ => a i + w^2) z)^2 = branchQ1 a i z := by
  unfold q1 branchQ1
  rw [mul_assoc, finite_q0_pullback a i z hz]

theorem infinity_q0_pullback (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    q0 a (1/z^2) * (deriv (fun w : ℂ => 1/w^2) z)^2 = infinityQ0 a z := by
  rw [infinity_map_derivative z hz]
  unfold q0 infinityQ0
  rw [infinity_polynomial_pullback a z hz]
  by_cases hd : infinityDen a z = 0
  · simp [hd]
  · field_simp
    ring

theorem infinity_q1_pullback (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    q1 a (1/z^2) * (deriv (fun w : ℂ => 1/w^2) z)^2 = infinityQ1 a z := by
  unfold q1
  rw [mul_assoc, infinity_q0_pullback a z hz]
  unfold infinityQ0 infinityQ1
  by_cases hd : infinityDen a z = 0
  · simp [hd]
  · field_simp

/-- The projective transition is valid even at infinity z=0. -/
theorem infinity_transition (a : Fin 4 → ℂ) (z : ℂ) :
    infinityQ0 a z = z^2 * infinityQ1 a z := by
  unfold infinityQ0 infinityQ1
  ring

/-- Exact rational ratio, valid off the divisor, rather than unrelated section values. -/
theorem source_ratio (a : Fin 4 → ℂ) (t : ℂ) (ht : contactPolynomial a t ≠ 0) :
    q1 a t / q0 a t = t := by
  have hq : q0 a t ≠ 0 := one_div_ne_zero ht
  unfold q1
  exact mul_div_cancel_right₀ t hq

/-- The same rational t ratio in the finite-branch trivialization. -/
theorem branch_ratio (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ)
    (hd : branchDen a i z ≠ 0) : branchQ1 a i z / branchQ0 a i z = a i + z^2 := by
  have hq : branchQ0 a i z ≠ 0 := div_ne_zero (by norm_num) hd
  unfold branchQ1
  exact mul_div_cancel_right₀ _ hq

/-- The infinity transition recovers t=1/z² off the center exactly. -/
theorem infinity_ratio (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hd : infinityDen a z ≠ 0) : infinityQ1 a z / infinityQ0 a z = 1/z^2 := by
  unfold infinityQ0 infinityQ1
  field_simp

end BicanonicalCharts318
#print axioms BicanonicalCharts318.finite_q0_pullback
#print axioms BicanonicalCharts318.finite_q1_pullback
#print axioms BicanonicalCharts318.infinity_q0_pullback
#print axioms BicanonicalCharts318.infinity_q1_pullback
#print axioms BicanonicalCharts318.infinity_transition
#print axioms BicanonicalCharts318.source_ratio
