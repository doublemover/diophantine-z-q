module
public import RiemannMappingBiholomorph318
public section
noncomputable section
namespace RiemannChartDerivative318
open Set Metric Filter Topology
set_option maxHeartbeats 1800000

/-- An actual biholomorphic partial homeomorphism has nonzero derivative;
this follows from differentiating its literal inverse identity. -/
theorem inverse_derivative (e : OpenPartialHomeomorph ℂ ℂ) {z : ℂ}
    (hz : z∈e.source) (he : AnalyticAt ℂ e z)
    (hi : AnalyticAt ℂ e.symm (e z)) :
    deriv e.symm (e z)*deriv e z=1 := by
  have hc := hi.differentiableAt.hasDerivAt.comp z he.differentiableAt.hasDerivAt
  have hid : (fun w => e.symm (e w))=ᶠ[𝓝 z] (fun w => w) := by
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact e.left_inv hw
  exact (hc.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id z)

theorem derivative_ne_zero (e : OpenPartialHomeomorph ℂ ℂ) {z : ℂ}
    (hz : z∈e.source) (he : AnalyticAt ℂ e z)
    (hi : AnalyticAt ℂ e.symm (e z)) : deriv e z≠0 := by
  intro h
  have hh := inverse_derivative e hz he hi
  rw [h,mul_zero] at hh
  exact zero_ne_one hh

@[expose] def phase (d : ℂ) : ℂ := (‖d‖:ℂ)/d

lemma phase_norm (d : ℂ) (hd : d≠0) : ‖phase d‖=1 := by
  simp only [phase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg d)]
  exact div_self (norm_ne_zero_iff.mpr hd)

lemma phase_mul (d : ℂ) (hd : d≠0) : phase d*d=(‖d‖:ℂ) :=
  div_mul_cancel₀ _ hd

/-- Unit phase rotation is bijective on the SAME unit disk. -/
theorem phase_disk_bijective (d : ℂ) (hd : d≠0) :
    BijOn (fun w : ℂ => phase d*w) (ball 0 1) (ball 0 1) := by
  have hp : phase d≠0 := by
    intro h
    have hh := phase_norm d hd
    rw [h,norm_zero] at hh
    exact zero_ne_one hh
  refine ⟨?_,?_,?_⟩
  · intro w hw
    simpa only [Metric.mem_ball,dist_zero_right,norm_mul,phase_norm d hd,one_mul] using hw
  · intro w hw v hv h
    exact mul_left_cancel₀ hp h
  · intro w hw
    refine ⟨w/phase d,?_,by field_simp [hp]⟩
    simpa only [Metric.mem_ball,dist_zero_right,norm_div,phase_norm d hd,div_one] using hw
end RiemannChartDerivative318
