module
public import MetricSmoothExtension318
public import Mathlib.Analysis.Calculus.Deriv.Inv
public section
noncomputable section
namespace MetricPullback318
open MetricSmoothExtension318
open scoped BigOperators
set_option maxHeartbeats 0

/-- The literal metric coefficient in the quotient t-coordinate. -/
@[expose] def sourceCoefficient (a : Fin 4 → ℂ) (t : ℂ) : ℝ :=
  (1 + ∑ j, ‖t - a j‖) / ∏ j, ‖t - a j‖

theorem infinity_distance (a z : ℂ) (hz : z ≠ 0) :
    ‖1 / z^2 - a‖ = ‖1 - a*z^2‖ / ‖z‖^2 := by
  have he : (1 : ℂ) / z^2 - a = (1 - a*z^2) / z^2 := by field_simp
  rw [he, norm_div, norm_pow]

theorem infinity_map_derivative (z : ℂ) (hz : z ≠ 0) :
    deriv (fun w : ℂ => 1 / w^2) z = -2 / z^3 := by
  have hf : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using hasDerivAt_pow 2 z
  have hd := ((hasDerivAt_const z (1 : ℂ)).div hf (pow_ne_zero 2 hz)).deriv
  calc
    _ = (0 * z^2 - 1 * (2*z)) / (z^2)^2 := hd
    _ = -2 / z^3 := by field_simp; ring

/-- Exact punctured infinity pullback; no asymptotic model is substituted. -/
theorem infinity_pullback (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    sourceCoefficient a (1 / z^2) * ‖-2 / z^3‖^2 = infinityCoefficient a z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs : (∑ j, ‖1 / z^2 - a j‖) = (∑ j, ‖1 - a j*z^2‖) / ‖z‖^2 := by
    simp_rw [infinity_distance _ _ hz]
    rw [Finset.sum_div]
  have hp : (∏ j, ‖1 / z^2 - a j‖) = (∏ j, ‖1 - a j*z^2‖) / (‖z‖^2)^4 := by
    simp_rw [infinity_distance _ _ hz]
    rw [Finset.prod_div_distrib]
    simp
  unfold sourceCoefficient infinityCoefficient
  rw [hs, hp, norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
  generalize hS : (∑ j, ‖1 - a j*z^2‖) = S
  generalize hP : (∏ j, ‖1 - a j*z^2‖) = P
  by_cases hden : P = 0
  · simp [hden]
  · field_simp
    ring

/-- The coefficient is exactly the pullback by the actual complex derivative. -/
theorem infinity_actual_pullback (a : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) :
    sourceCoefficient a (1 / z^2) * ‖deriv (fun w : ℂ => 1 / w^2) z‖^2 =
      infinityCoefficient a z := by
  rw [infinity_map_derivative z hz]
  exact infinity_pullback a z hz

/-- Splitting the four contacts into one chosen branch and the remaining three. -/
theorem source_branch (a : Fin 4 → ℂ) (i : Fin 4) (w : ℂ) :
    sourceCoefficient a (a i + w) =
      branchBase (fun j : {j : Fin 4 // j ≠ i} => a i - a j) w := by
  classical
  have he (j : Fin 4) : a i + w - a j = a i - a j + w := by ring
  have hs : (∑ j : Fin 4, ‖a i + w - a j‖) =
      ‖w‖ + ∑ j : {j : Fin 4 // j ≠ i}, ‖a i - a j + w‖ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [add_sub_cancel_left]
    rw [add_comm]
    congr 1
    simp_rw [he]
    exact Finset.sum_subtype (Finset.univ.erase i) (by simp) (fun j => ‖a i - a j + w‖)
  have hp : (∏ j : Fin 4, ‖a i + w - a j‖) =
      ‖w‖ * ∏ j : {j : Fin 4 // j ≠ i}, ‖a i - a j + w‖ := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [add_sub_cancel_left]
    rw [mul_comm]
    congr 1
    simp_rw [he]
    exact Finset.prod_subtype (Finset.univ.erase i) (by simp) (fun j => ‖a i - a j + w‖)
  unfold sourceCoefficient branchBase
  rw [hs, hp]
  congr 1
  ring

/-- Exact actual pullback at every finite branch of the four-contact model. -/
theorem branch_actual_pullback (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ) (hz : z ≠ 0) :
    sourceCoefficient a (a i + z^2) * ‖deriv (fun w : ℂ => a i + w^2) z‖^2 =
      branchCoefficient (fun j : {j : Fin 4 // j ≠ i} => a i - a j) z := by
  rw [source_branch, branch_map_derivative]
  exact branch_pullback _ z hz

end MetricPullback318
#print axioms MetricPullback318.infinity_pullback
#print axioms MetricPullback318.infinity_actual_pullback
#print axioms MetricPullback318.source_branch
#print axioms MetricPullback318.branch_actual_pullback
