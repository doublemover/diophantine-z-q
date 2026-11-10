module
public import LocalHolomorphicSquareRoot318
public import FiniteAnalyticCharts318
public import Mathlib.Analysis.Analytic.Order
public section
noncomputable section
namespace AnalyticSquaredBaseChange318
open Filter
open scoped Topology

/-- A genuine noncritical analytic change of BASE coordinate preserves the
local square model after a constructed analytic invertible SOURCE change.
The new source coordinate and its inverse are produced, not assumed. -/
theorem normalize (f:ℂ→ℂ) (hf:AnalyticAt ℂ f 0) (h0:f 0=0) (hd:deriv f 0≠0) :
    ∃q k:ℂ→ℂ, AnalyticAt ℂ q 0 ∧ q 0=0 ∧ deriv q 0≠0 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun z=>k (q z)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (fun z=>q (k z)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ z in 𝓝 (0:ℂ),q z^2=f (z^2)) := by
  have ho:analyticOrderAt f 0=(1:ℕ):=hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 hd
  obtain ⟨u,hu,hu0,he⟩:=hf.analyticOrderAt_eq_natCast.mp ho
  have he':∀ᶠ z in 𝓝 (0:ℂ),f z=z*u z:=by
    simpa only [sub_zero,pow_one,smul_eq_mul] using he
  let b:ℂ:=Complex.sqrt (u 0)
  have hb:b^2=u 0:=LocalHolomorphicSquareRoot318.sqrt_square _
  have hb0:b≠0:=by
    intro hz
    apply hu0
    rw [←hb,hz,zero_pow (by decide : 2≠0)]
  obtain ⟨s,hs,hs0,hsq⟩:=LocalHolomorphicSquareRoot318.exists_local_root u 0 b hu hu0 hb
  let q:ℂ→ℂ:=fun z=>z*s (z^2)
  have hsqA:AnalyticAt ℂ (fun z:ℂ=>s (z^2)) 0:=by
    have hpow:AnalyticAt ℂ (fun z:ℂ=>z^2) 0:=analyticAt_id.pow 2
    have hs':AnalyticAt ℂ s ((0:ℂ)^2):=by simpa using hs
    exact hs'.comp hpow
  have hq:AnalyticAt ℂ q 0:=analyticAt_id.mul hsqA
  have hq0:q 0=0:=by simp [q]
  have hqd:HasDerivAt q b 0:=by
    have hh:=(hasDerivAt_id (0:ℂ)).mul hsqA.differentiableAt.hasDerivAt
    simpa only [q,zero_pow (by decide : 2≠0),hs0,one_mul,zero_mul,add_zero] using hh
  have hqne:deriv q 0≠0:=by rw [hqd.deriv];exact hb0
  obtain ⟨k,hk,hk0,hl,hr⟩:=FiniteAnalyticCharts318.analytic_inverse hq hqne
  rw [hq0] at hk hk0 hr
  refine ⟨q,k,hq,hq0,hqne,hk,hk0,hl,hr,?_⟩
  have ht:Tendsto (fun z:ℂ=>z^2) (𝓝 0) (𝓝 0):=by
    simpa using (continuousAt_id.pow 2 : ContinuousAt (fun z:ℂ=>z^2) 0)
  filter_upwards [ht.eventually he'] with z hz
  dsimp [q]
  rw [mul_pow,hsq,hz]
end AnalyticSquaredBaseChange318
