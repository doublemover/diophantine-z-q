module
public import MetricPullback318
public import ConformalCurvature318
public section
noncomputable section
namespace LiteralMetricExtension318
open MetricSmoothExtension318 MetricPullback318 ConformalCurvature318
open scoped ContDiff Topology
set_option maxHeartbeats 0

@[expose] def contacts : Fin 4 → ℂ := ![0, 32, 76832, -343]

theorem contacts_injective : Function.Injective contacts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [contacts] at *

/-- Actual C∞ complex-coordinate coefficients give the exact real-axis C²
input consumed by the curvature and compact-comparison packets. -/
theorem smooth_axisC2 (f : ℂ → ℝ) (hf : ContDiffAt ℝ ∞ f 0) :
    AxisC2 (fun z : ℝ × ℝ => f ((z.1 : ℂ) + z.2 * Complex.I)) := by
  have hf2 : ContDiffAt ℝ 2 f 0 := hf.of_le (by norm_num)
  have hx : ContDiffAt ℝ 2 (fun t : ℝ => (t : ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt
  have hy : ContDiffAt ℝ 2 (fun t : ℝ => (t : ℂ) * Complex.I) 0 := hx.mul contDiffAt_const
  constructor
  · simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] using hf2.comp (f := fun t : ℝ => (t : ℂ)) 0 hx
  · have hfY : ContDiffAt ℝ 2 f ((0 : ℂ) * Complex.I) := by simpa using hf2
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using
      hfY.comp (f := fun t : ℝ => (t : ℂ) * Complex.I) 0 hy

/-- Every actual finite branch has a smooth strictly positive extension. -/
theorem finite_branch_extension (i : Fin 4) :
    ContDiffAt ℝ ∞ (branchCoefficient
      (fun j : {j : Fin 4 // j ≠ i} => contacts i - contacts j)) 0 ∧
    0 < branchCoefficient (fun j : {j : Fin 4 // j ≠ i} => contacts i - contacts j) 0 := by
  have hb (j : {j : Fin 4 // j ≠ i}) : contacts i - contacts j ≠ 0 :=
    sub_ne_zero.mpr (contacts_injective.ne (Ne.symm j.property))
  exact ⟨branchCoefficient_smooth _ hb, branchCoefficient_pos _ hb⟩

/-- The actual finite branch coefficient equals the actual punctured pullback. -/
theorem finite_branch_pullback (i : Fin 4) (z : ℂ) (hz : z ≠ 0) :
    sourceCoefficient contacts (contacts i + z^2) *
      ‖deriv (fun w : ℂ => contacts i + w^2) z‖^2 =
      branchCoefficient (fun j : {j : Fin 4 // j ≠ i} => contacts i - contacts j) z :=
  branch_actual_pullback contacts i z hz

/-- Infinity is also smooth and positive, with exact coefficient sixteen. -/
theorem infinity_extension :
    ContDiffAt ℝ ∞ (infinityCoefficient contacts) 0 ∧
    infinityCoefficient contacts 0 = 16 ∧ 0 < infinityCoefficient contacts 0 :=
  ⟨infinityCoefficient_smooth _, infinityCoefficient_zero _, infinityCoefficient_pos _⟩

theorem infinity_pullback (z : ℂ) (hz : z ≠ 0) :
    sourceCoefficient contacts (1 / z^2) * ‖deriv (fun w : ℂ => 1 / w^2) z‖^2 =
      infinityCoefficient contacts z := infinity_actual_pullback contacts z hz

theorem finite_branch_axisC2 (i : Fin 4) :
    AxisC2 (fun z : ℝ × ℝ => branchCoefficient
      (fun j : {j : Fin 4 // j ≠ i} => contacts i - contacts j)
        ((z.1 : ℂ) + z.2 * Complex.I)) :=
  smooth_axisC2 _ (finite_branch_extension i).1

theorem infinity_axisC2 :
    AxisC2 (fun z : ℝ × ℝ => infinityCoefficient contacts
      ((z.1 : ℂ) + z.2 * Complex.I)) := smooth_axisC2 _ infinity_extension.1

end LiteralMetricExtension318
#print axioms LiteralMetricExtension318.finite_branch_extension
#print axioms LiteralMetricExtension318.infinity_extension
#print axioms LiteralMetricExtension318.finite_branch_axisC2
#print axioms LiteralMetricExtension318.infinity_axisC2
