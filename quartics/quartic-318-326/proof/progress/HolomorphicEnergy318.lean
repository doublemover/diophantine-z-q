module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
public import Mathlib.Tactic
public section
noncomputable section
open Set MeasureTheory Metric
namespace HolomorphicEnergy318
set_option maxHeartbeats 0

/-- The real area Jacobian of complex multiplication is its squared norm. -/
theorem complex_jacobian (a:ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).det = ‖a‖^2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- The actual complex derivative, restricted to real scalars, is the area
change-of-variables derivative. -/
theorem real_derivative {F:ℂ→ℂ} {z:ℂ} (hF:DifferentiableAt ℂ F z) :
    HasFDerivAt F ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ) z :=
  hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ

/-- Exact ordinary-area energy transport for an injective holomorphic chart.
Neither the local coefficient estimate nor a Jacobian factor is assumed. -/
theorem integral_pullback (F f:ℂ→ℂ) (s:Set ℂ) (hs:IsOpen s)
    (hF:DifferentiableOn ℂ F s) (hinj:InjOn F s) :
    (∫z in s, ‖f (F z)*deriv F z‖^2) = ∫w in F '' s, ‖f w‖^2 := by
  have hd (z:ℂ) (hz:z∈s) := (real_derivative ((hF z hz).differentiableAt (hs.mem_nhds hz))).hasFDerivWithinAt (s:=s)
  have hc := integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet hd hinj
    (fun w:ℂ=> ‖f w‖^2)
  rw [hc]
  apply setIntegral_congr_fun hs.measurableSet
  intro z hz
  dsimp only
  rw [complex_jacobian,abs_of_nonneg (sq_nonneg _),smul_eq_mul,norm_mul,mul_pow]
  ring

/-- Integrability is transported by the same actual chart, including the
Jacobian in the pulled-back differential coefficient. -/
theorem integrable_pullback_iff (F f:ℂ→ℂ) (s:Set ℂ) (hs:IsOpen s)
    (hF:DifferentiableOn ℂ F s) (hinj:InjOn F s) :
    IntegrableOn (fun z=> ‖f (F z)*deriv F z‖^2) s ↔
      IntegrableOn (fun w=> ‖f w‖^2) (F '' s) := by
  have hd (z:ℂ) (hz:z∈s) := (real_derivative ((hF z hz).differentiableAt (hs.mem_nhds hz))).hasFDerivWithinAt (s:=s)
  have hc := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs.measurableSet hd hinj
    (fun w:ℂ=> ‖f w‖^2)
  convert hc.symm using 2
  funext z
  rw [complex_jacobian,abs_of_nonneg (sq_nonneg _),smul_eq_mul,norm_mul,mul_pow]
  ring

/-- Restrict global nonnegative differential energy along an actual chart.
Global energy is on a possibly larger measurable region, not an assumed
bound on the local coefficient. -/
theorem pullback_energy_le (F f:ℂ→ℂ) (s t:Set ℂ) (hs:IsOpen s)
    (hF:DifferentiableOn ℂ F s) (hinj:InjOn F s) (himage:F '' s ⊆ t)
    (hfi:IntegrableOn (fun w=>‖f w‖^2) t) :
    IntegrableOn (fun z=>‖f (F z)*deriv F z‖^2) s ∧
      (∫z in s,‖f (F z)*deriv F z‖^2) ≤ ∫w in t,‖f w‖^2 := by
  constructor
  · exact (integrable_pullback_iff F f s hs hF hinj).mpr (hfi.mono_set himage)
  · rw [integral_pullback F f s hs hF hinj]
    exact setIntegral_mono_set hfi (Filter.Eventually.of_forall (fun w=>sq_nonneg ‖f w‖))
      (Filter.Eventually.of_forall (fun w hw=>himage hw))

/-- A norm-one differential gives both genuine local integrability and the
ordinary energy bound required by the Wronskian theorem. -/
theorem pullback_energy_one (F f:ℂ→ℂ) (c:ℂ) (rho:ℝ) (t:Set ℂ)
    (hF:DifferentiableOn ℂ F (ball c rho)) (hinj:InjOn F (ball c rho))
    (himage:F '' ball c rho ⊆ t) (hfi:IntegrableOn (fun w=>‖f w‖^2) t)
    (hglobal:(∫w in t,‖f w‖^2)≤1) :
    IntegrableOn (fun z=>‖f (F z)*deriv F z‖^2) (ball c rho) ∧
      (∫z in ball c rho,‖f (F z)*deriv F z‖^2)≤1 := by
  obtain ⟨hi,he⟩ := pullback_energy_le F f (ball c rho) t isOpen_ball hF hinj himage hfi
  exact ⟨hi,he.trans hglobal⟩

end HolomorphicEnergy318
#print axioms HolomorphicEnergy318.complex_jacobian
#print axioms HolomorphicEnergy318.integral_pullback
#print axioms HolomorphicEnergy318.pullback_energy_one
