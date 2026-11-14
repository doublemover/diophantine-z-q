module
public import BoundedVertexExtension318
public import FiniteAnalyticCharts318
public import Mathlib.Analysis.Calculus.Deriv.Slope
public section
noncomputable section
namespace PuncturedSquareCoordinate318
open Set Filter Function
open scoped Topology

/-- A punctured map respecting the SAME simple-branch square coordinate
has a constructed analytic extension with invertible derivative. Neither
continuity at the missing branch point nor a sign choice is a premise. -/
theorem extend (f:ℂ→ℂ)
    (hd:∀ᶠ z in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ f z)
    (hs:∀ᶠ z in 𝓝[≠] (0:ℂ),f z^2=z^2) :
    ∃q k:ℂ→ℂ,AnalyticAt ℂ q 0 ∧ q 0=0 ∧
      q=ᶠ[𝓝[≠] (0:ℂ)] f ∧ deriv q 0^2=1 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun z=>k (q z))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun z=>q (k z))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ z in 𝓝 (0:ℂ),q z^2=z^2) := by
  have hn:∀ᶠ z in 𝓝[≠] (0:ℂ),‖f z‖=‖z‖:=by
    filter_upwards [hs] with z hz
    have hh:=congrArg norm hz
    simp only [norm_pow] at hh
    nlinarith [norm_nonneg (f z),norm_nonneg z]
  have ht:Tendsto f (𝓝[≠] (0:ℂ)) (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh:Tendsto (fun z:ℂ=>‖z‖) (𝓝[≠] (0:ℂ)) (𝓝 0):=by
      simpa using continuous_norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hh.congr' hn.symm
  let q:ℂ→ℂ:=update f 0 0
  have hq0:q 0=0:=by simp [q]
  have hqf:q=ᶠ[𝓝[≠] (0:ℂ)] f:=by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [q,update_of_ne hz]
  have hc:ContinuousAt q 0:=continuousAt_update_same.mpr ht
  have hdq:∀ᶠ z in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ q z:=by
    filter_upwards [hd,self_mem_nhdsWithin] with z hz hne
    apply hz.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hne] with w hw
    simp only [q,update_of_ne hw]
  have hq:AnalyticAt ℂ q 0:=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdq hc
  have hqs:∀ᶠ z in 𝓝 (0:ℂ),q z^2=z^2:=by
    have hsn:=eventually_nhdsWithin_iff.mp hs
    filter_upwards [hsn] with z hz
    by_cases h:z=0
    · simp [h,hq0]
    · simpa only [q,update_of_ne h] using hz h
  have hderiv:Tendsto (fun z:ℂ=>q z/z) (𝓝[≠] (0:ℂ)) (𝓝 (deriv q 0)):=by
    simpa [slope,hq0,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hq.differentiableAt.hasDerivAt.tendsto_slope
  have hratio:∀ᶠ z in 𝓝[≠] (0:ℂ),(q z/z)^2=(1:ℂ):=by
    filter_upwards [hqs.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hne
    rw [div_pow,hz,div_self (pow_ne_zero 2 hne)]
  have hds:deriv q 0^2=(1:ℂ):=
    tendsto_nhds_unique (hderiv.pow 2) (tendsto_const_nhds.congr' hratio.symm)
  have hdn:deriv q 0≠0:=by
    intro h
    rw [h,zero_pow (by decide:2≠0)] at hds
    exact zero_ne_one hds
  obtain ⟨k,hk,hk0,hl,hr⟩:=FiniteAnalyticCharts318.analytic_inverse hq hdn
  rw [hq0] at hk hk0 hr
  exact ⟨q,k,hq,hq0,hqf,hds,hk,hk0,hl,hr,hqs⟩
end PuncturedSquareCoordinate318
