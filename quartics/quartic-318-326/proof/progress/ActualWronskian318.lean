module
public import HolomorphicDisk318
public import WronskianCoefficient318
public import Mathlib.MeasureTheory.Group.Integral
public section
noncomputable section
open Set MeasureTheory Metric
open scoped Real
namespace ActualWronskian318
set_option maxHeartbeats 0

 theorem shift_indicator (F:ℂ→ℝ) (c:ℂ) (rho:ℝ) (z:ℂ) :
    (ball c rho).indicator F (c+z) =
      (ball 0 rho).indicator (fun w=>F (c+w)) z := by
  simp [Set.indicator,mem_ball,dist_eq_norm]

 theorem shifted_integrable (F:ℂ→ℝ) (c:ℂ) (rho:ℝ)
    (hi:IntegrableOn F (ball c rho)) :
    IntegrableOn (fun z:ℂ=>F (c+z)) (ball 0 rho) := by
  apply (integrable_indicator_iff measurableSet_ball).mp
  have hc:=((integrable_indicator_iff measurableSet_ball).mpr hi).comp_add_left c
  simpa only [shift_indicator] using hc

 theorem shifted_integral (F:ℂ→ℝ) (c:ℂ) (rho:ℝ) :
    (∫z in ball (0:ℂ) rho,F (c+z)) = ∫z in ball c rho,F z := by
  have he:=integral_add_left_eq_self (μ:=volume) ((ball c rho).indicator F) c
  simpa only [shift_indicator,integral_indicator measurableSet_ball] using he

/-- The sharp factorial-normalized coefficient bound from actual area L²
normalization on the holomorphic disc centered at c. -/
theorem local_coefficient (f:ℂ→ℂ) (c:ℂ) (rho:ℝ) (hrho:0<rho)
    (hf:DifferentiableOn ℂ f (ball c rho))
    (hfi:IntegrableOn (fun z:ℂ=>‖f z‖^2) (ball c rho))
    (hL2:(∫z in ball c rho,‖f z‖^2)≤1) (j:ℕ) :
    ‖iteratedDeriv j f c/(j.factorial:ℂ)‖ ≤
      Real.sqrt ((j+1:ℝ)/Real.pi)*(rho⁻¹)^(j+1) := by
  apply HolomorphicDisk318.coefficient_bound f c rho hrho hf
    (shifted_integrable _ c rho hfi)
  rw [shifted_integral (fun z=>‖f z‖^2) c rho]
  exact hL2

/-- Actual holomorphic differentials with local area energy at most one
satisfy the factorial-normalized Wronskian estimate. No coefficient,
Wronskian, or Hadamard bound is supplied as a premise. -/
theorem local_wronskian_bound (g:ℕ) (hg:1≤g) (N rho:ℝ) (hN:1≤N)
    (hr:Real.exp (-21)/N≤rho) (f:Fin g→ℂ→ℂ) (b:ℂ)
    (hf:∀i,DifferentiableOn ℂ (f i) (ball b rho))
    (hfi:∀i,IntegrableOn (fun z:ℂ=>‖f i z‖^2) (ball b rho))
    (hL2:∀i,(∫z in ball b rho,‖f i z‖^2)≤1) :
    Real.log ‖WronskianFinite318.wronskian g f b‖≤
      100*(g:ℝ)^2*Real.log (2*g*N) := by
  apply WronskianCoefficient318.actual_wronskian_bound g hg N rho hN hr f b
  intro i j
  exact local_coefficient (f i) b rho
    (WronskianCoefficient318.radius_inverse_bound N rho hN hr).1
    (hf i) (hfi i) (hL2 i) j.val

end ActualWronskian318
#print axioms ActualWronskian318.local_coefficient
#print axioms ActualWronskian318.local_wronskian_bound
