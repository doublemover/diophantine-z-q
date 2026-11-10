module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.RemovableSingularity
public section
noncomputable section
namespace ComplexHolomorphicChartInverse318
open Filter Topology Set Metric
set_option maxHeartbeats 1500000

/-- A holomorphic local homeomorphism cannot have locally zero derivative.
This uses its actual local injectivity, not an assumed nonzero derivative. -/
theorem derivative_punctured (e : OpenPartialHomeomorph ℂ ℂ) {x : ℂ}
    (hx : x∈e.source) (he : AnalyticAt ℂ e x) :
    ∀ᶠ z in 𝓝[≠] x,deriv e z≠0 := by
  rcases he.deriv.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hnear : ∀ᶠ z in 𝓝 x,z∈e.source ∧ AnalyticAt ℂ e z ∧ deriv e z=0 :=
      (e.open_source.mem_nhds hx).and (he.eventually_analyticAt.and hzero)
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hconst : ∀ z∈ball x r,e z=e x := by
      intro z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
        (fun w hw => (hball hw).2.1.differentiableAt.differentiableWithinAt)
        (fun w hw => (hball hw).2.2) hz (mem_ball_self hr)
    have hf : ∀ᶠ z in 𝓝[≠] x,False := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds x hr),
        self_mem_nhdsWithin] with z hz hzx
      have hzx' := e.injOn (hball hz).1 hx (hconst z hz)
      exact hzx hzx'
    obtain ⟨z,hz⟩ := hf.exists
    exact hz
  · exact hne

/-- Away from a zero derivative, the inverse of the SAME partial
homeomorphism is analytic by the analytic inverse-function theorem. -/
theorem inverse_of_derivative (e : OpenPartialHomeomorph ℂ ℂ) {x : ℂ}
    (hx : x∈e.source) (he : AnalyticAt ℂ e x) (hd : deriv e x≠0) :
    AnalyticAt ℂ e.symm (e x) := by
  apply (analyticAt_comp_iff_of_deriv_ne_zero he hd).mp
  apply analyticAt_id.congr
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact (e.left_inv hz).symm

/-- Holomorphic inverse for an actual complex partial homeomorphism,
including an apparently critical center. Isolated zeros and removable
singularities remove any extra derivative hypothesis. -/
theorem inverse_analytic (e : OpenPartialHomeomorph ℂ ℂ) {x : ℂ}
    (hx : x∈e.source) (he : AnalyticAt ℂ e x) :
    AnalyticAt ℂ e.symm (e x) := by
  have hy := e.map_source hx
  have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm hy
  have hto : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa only [e.left_inv hx] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (e.open_target.mem_nhds hy),self_mem_nhdsWithin] with z hz hzx
      intro hz'
      apply hzx
      calc z=e (e.symm z) := (e.right_inv hz).symm
           _=e x := congrArg e hz'
  have hsource : ∀ᶠ z in 𝓝[≠] x,z∈e.source ∧ AnalyticAt ℂ e z :=
    eventually_nhdsWithin_of_eventually_nhds
      ((e.open_source.mem_nhds hx).and he.eventually_analyticAt)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hto.eventually (hsource.and (derivative_punctured e hx he)),
    eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hy)] with z hz hzt
  have ha := inverse_of_derivative e hz.1.1 hz.1.2 hz.2
  rw [e.right_inv hzt] at ha
  exact ha.differentiableAt
end ComplexHolomorphicChartInverse318
