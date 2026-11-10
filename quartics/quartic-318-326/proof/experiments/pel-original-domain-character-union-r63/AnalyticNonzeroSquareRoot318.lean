module
public import FiniteAnalyticCharts318
public import Mathlib.Analysis.Complex.BranchLogRoot
public section
noncomputable section
namespace AnalyticNonzeroSquareRoot318
open Set Filter
open scoped Topology
set_option maxHeartbeats 700000

/-- A continuous square root of a nonvanishing holomorphic function is
holomorphic. Nonzero derivative of squaring is DERIVED from the equation;
no holomorphy of an arbitrary pointwise square-root choice is assumed. -/
theorem analytic_root {U:Set ℂ} (hU:IsOpen U) {g s:ℂ→ℂ}
    (hg:AnalyticOnNhd ℂ g U) (hs:ContinuousOn s U)
    (he:∀z,s z^2=g z) (hn:∀z∈U,g z≠0) : AnalyticOnNhd ℂ s U := by
  intro z hz
  have hs0:s z≠0:=by
    intro hh
    have hez:=he z
    rw [hh,zero_pow (by decide : 2≠0)] at hez
    exact hn z hz hez.symm
  have hfa:AnalyticAt ℂ (fun w:ℂ=>w^2) (s z):=analyticAt_id.pow 2
  have hd:deriv (fun w:ℂ=>w^2) (s z)≠0:=by
    rw [((hasDerivAt_id (s z)).pow 2).deriv]
    simpa using mul_ne_zero (by norm_num : (2:ℂ)≠0) hs0
  obtain ⟨k,hk,_,hl,_⟩:=FiniteAnalyticCharts318.analytic_inverse hfa hd
  have hcs:ContinuousAt s z:=(hs z hz).continuousAt (hU.mem_nhds hz)
  have hleft:(fun w=>k (g w)) =ᶠ[𝓝 z] s := by
    filter_upwards [hcs.eventually hl] with w hw
    simpa only [he,Function.id_def] using hw
  have hkg:AnalyticAt ℂ k (g z):=by rw [←he z]; exact hk
  exact (hkg.comp (hg z hz)).congr hleft

/-- Pinned simply-connected covering lifting first gives a CONTINUOUS
root; the preceding inverse-function argument upgrades the actual same
root to a holomorphic one. The equation holds globally, analyticity on U. -/
theorem exists_analytic_root {U:Set ℂ} (hU:IsOpen U) (hUc:IsSimplyConnected U)
    {g:ℂ→ℂ} (hg:AnalyticOnNhd ℂ g U) (hn:∀z∈U,g z≠0) :
    ∃s:ℂ→ℂ,AnalyticOnNhd ℂ s U ∧ ∀z,s z^2=g z := by
  have hzero:0∉g '' U:=by
    rintro ⟨z,hz,he⟩
    exact hn z hz he
  obtain ⟨s,hs,he⟩:=Complex.exists_continuousOn_pow_eq hUc hU hg.continuousOn hzero
    (by decide : 2≠0)
  exact ⟨s,analytic_root hU hg hs he hn,he⟩
end AnalyticNonzeroSquareRoot318
