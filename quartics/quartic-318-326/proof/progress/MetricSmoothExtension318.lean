module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic
public section
noncomputable section
namespace MetricSmoothExtension318
open scoped BigOperators ContDiff
set_option maxHeartbeats 0
variable {ι : Type*} [Fintype ι]

/-- The literal finite-branch pulled-back metric coefficient. -/
@[expose] def branchCoefficient (b : ι → ℂ) (z : ℂ) : ℝ :=
  4 * (1 + ‖z‖^2 + ∑ j, ‖b j + z^2‖) / ∏ j, ‖b j + z^2‖

/-- The source metric after translating one branch value to zero. -/
@[expose] def branchBase (b : ι → ℂ) (w : ℂ) : ℝ :=
  (1 + ‖w‖ + ∑ j, ‖b j + w‖) / (‖w‖ * ∏ j, ‖b j + w‖)

theorem branchCoefficient_smooth (b : ι → ℂ) (hb : ∀ j, b j ≠ 0) :
    ContDiffAt ℝ ∞ (branchCoefficient b) 0 := by
  have hf (j : ι) : ContDiffAt ℝ ∞ (fun z : ℂ => ‖b j + z^2‖) 0 := by
    apply ContDiffAt.norm (𝕜 := ℂ)
    · fun_prop
    · simpa using hb j
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖^2) 0 := contDiffAt_id.norm_sq (𝕜 := ℂ)
  have hs := ContDiffAt.sum (s := Finset.univ) (fun j _ => hf j)
  have hp := contDiffAt_prod (t := Finset.univ) (fun j _ => hf j)
  have hz : (∏ j, ‖b j + (0 : ℂ)^2‖) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simpa using norm_ne_zero_iff.mpr (hb j)
  exact (contDiffAt_const.mul ((contDiffAt_const.add hn).add hs)).div hp hz

theorem branchCoefficient_pos (b : ι → ℂ) (hb : ∀ j, b j ≠ 0) :
    0 < branchCoefficient b 0 := by
  unfold branchCoefficient
  apply div_pos
  · positivity
  · apply Finset.prod_pos
    intro j _
    simpa using norm_pos_iff.mpr (hb j)

/-- Exact punctured pullback under w=z², including the actual derivative factor. -/
theorem branch_pullback (b : ι → ℂ) (z : ℂ) (hz : z ≠ 0) :
    branchBase b (z^2) * ‖2*z‖^2 = branchCoefficient b z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  unfold branchBase branchCoefficient
  rw [norm_pow, norm_mul]
  norm_num only [Complex.norm_ofNat]
  by_cases hp : (∏ j, ‖b j + z^2‖) = 0
  · simp [hp]
  · field_simp
    ring

theorem branch_map_derivative (a z : ℂ) : deriv (fun w : ℂ => a + w^2) z = 2*z := by
  simpa using (((hasDerivAt_id z).pow 2).const_add a).deriv

/-- The literal infinity-chart coefficient, with the crucial |z|² term. -/
@[expose] def infinityCoefficient (a : Fin 4 → ℂ) (z : ℂ) : ℝ :=
  4 * (‖z‖^2 + ∑ j, ‖1 - a j * z^2‖) / ∏ j, ‖1 - a j * z^2‖

theorem infinityCoefficient_smooth (a : Fin 4 → ℂ) :
    ContDiffAt ℝ ∞ (infinityCoefficient a) 0 := by
  have hf (j : Fin 4) : ContDiffAt ℝ ∞ (fun z : ℂ => ‖1 - a j * z^2‖) 0 := by
    apply ContDiffAt.norm (𝕜 := ℂ)
    · fun_prop
    · norm_num
  have hn : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖^2) 0 := contDiffAt_id.norm_sq (𝕜 := ℂ)
  have hs := ContDiffAt.sum (s := Finset.univ) (fun j _ => hf j)
  have hp := contDiffAt_prod (t := Finset.univ) (fun j _ => hf j)
  have hz : (∏ j, ‖1 - a j * (0 : ℂ)^2‖) ≠ 0 := by norm_num
  exact (contDiffAt_const.mul (hn.add hs)).div hp hz

theorem infinityCoefficient_zero (a : Fin 4 → ℂ) : infinityCoefficient a 0 = 16 := by
  norm_num [infinityCoefficient]

theorem infinityCoefficient_pos (a : Fin 4 → ℂ) : 0 < infinityCoefficient a 0 := by
  rw [infinityCoefficient_zero]
  norm_num

end MetricSmoothExtension318
#print axioms MetricSmoothExtension318.branchCoefficient_smooth
#print axioms MetricSmoothExtension318.branchCoefficient_pos
#print axioms MetricSmoothExtension318.branch_pullback
#print axioms MetricSmoothExtension318.infinityCoefficient_smooth
#print axioms MetricSmoothExtension318.infinityCoefficient_zero
