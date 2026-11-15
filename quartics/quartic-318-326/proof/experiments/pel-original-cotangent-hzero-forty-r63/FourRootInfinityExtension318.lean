module
public import AnalyticSquareRemovable318
public import FiniteAnalyticCharts318
public import Mathlib.Tactic.FinCases
public section
noncomputable section
namespace FourRootInfinityExtension318
open Set Filter
open scoped Topology
@[expose] def parameter (r:Fin 4→ℂ→ℂ) (w:ℂ):ℂ:=w/r 0 w
@[expose] def ratio (r:Fin 4→ℂ→ℂ) (k:Fin 4) (w:ℂ):ℂ:=r k w/r 0 w

/-- Simultaneously normalize ALL original roots near infinity. The actual
local coordinate is1/z0 and the three sign ratios z_k/z0, not the singular
four-character fiber-product point. The eight possible infinity branches
retain their separate sign triples. -/
theorem extend (b:Fin 4→ℂ) (z:Fin 4→ℂ→ℂ)
    (hd:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ (z k) w)
    (he:∀k,∀ᶠw in 𝓝[≠] (0:ℂ),(z k w)^2=(w^2)⁻¹-b k) :
    ∃r:Fin 4→ℂ→ℂ,∃inv:ℂ→ℂ,
      (∀k,AnalyticAt ℂ (r k) 0) ∧ (∀k,(r k 0)^2=1) ∧
      (∀k,r k=ᶠ[𝓝[≠] (0:ℂ)] (fun w=>w*z k w)) ∧
      AnalyticAt ℂ (parameter r) 0 ∧ parameter r 0=0 ∧
      deriv (parameter r) 0^2=1 ∧
      AnalyticAt ℂ inv 0 ∧ inv 0=0 ∧
      (fun w=>inv (parameter r w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>parameter r (inv w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀k,AnalyticAt ℂ (ratio r k) 0 ∧ (ratio r k 0)^2=1) ∧
      (∀ᶠw in 𝓝 (0:ℂ),ratio r 0 w=1 ∧
        ∀k,(ratio r k w)^2=1+(b 0-b k)*(parameter r w)^2) ∧
      (∀ᶠw in 𝓝[≠] (0:ℂ),parameter r w=(z 0 w)⁻¹ ∧
        ∀k,ratio r k w=z k w/z 0 w) := by
  have allExt:∀k,∃R:ℂ→ℂ,AnalyticAt ℂ R 0 ∧
      R=ᶠ[𝓝[≠] (0:ℂ)] (fun w=>w*z k w) ∧ R 0^2=1 ∧
      (∀ᶠw in 𝓝 (0:ℂ),R w^2=1-b k*w^2):=by
    intro k
    have hkd:∀ᶠw in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ (fun w=>w*z k w) w:=by
      filter_upwards [hd k] with w hw
      exact differentiableAt_id.mul hw
    have hke:∀ᶠw in 𝓝[≠] (0:ℂ),(w*z k w)^2=1-b k*w^2:=by
      filter_upwards [he k,self_mem_nhdsWithin] with w hw hn
      have hwn : w≠0 := by
        simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hn
      rw [mul_pow,hw]
      field_simp [hwn]
      <;> ring
    obtain ⟨R,hR,hRz,h0,hall⟩:=AnalyticSquareRemovable318.extend (fun w=>w*z k w)
      (fun w=>1-b k*w^2) (analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))) hkd hke
    refine ⟨R,hR,hRz,?_,hall⟩
    simpa only [zero_pow (by decide:2≠0),mul_zero,sub_zero] using h0
  choose r hr hrz hr0 hrsq using allExt
  have hne:r 0 0≠0:=by
    intro h
    have hh:=hr0 0
    rw [h,zero_pow (by decide:2≠0)] at hh
    exact zero_ne_one hh
  have hunit:∀ᶠw in 𝓝 (0:ℂ),r 0 w≠0:=(hr 0).continuousAt.eventually_ne hne
  have hu:AnalyticAt ℂ (parameter r) 0:=analyticAt_id.div (hr 0) hne
  have hu0:parameter r 0=0:=by simp [parameter]
  have hud:HasDerivAt (parameter r) (1/r 0 0) 0:=by
    have h := (hasDerivAt_id (0:ℂ)).div (hr 0).differentiableAt.hasDerivAt hne
    change HasDerivAt (fun w : ℂ => w/r 0 w)
      ((1*r 0 0-0*deriv (r 0) 0)/(r 0 0)^2) 0 at h
    have hc : (1*r 0 0-0*deriv (r 0) 0)/(r 0 0)^2=1/r 0 0 := by
      field_simp [hne]
      <;> ring
    rw [hc] at h
    exact h
  have hud2:deriv (parameter r) 0^2=1:=by
    rw [hud.deriv,div_pow,hr0 0]
    norm_num
  have hudne:deriv (parameter r) 0≠0:=by
    intro h
    rw [h,zero_pow (by decide:2≠0)] at hud2
    exact zero_ne_one hud2
  obtain ⟨inv,hi,hi0,hleft,hright⟩:=FiniteAnalyticCharts318.analytic_inverse hu hudne
  rw [hu0] at hi hi0 hright
  have hratio:∀k,AnalyticAt ℂ (ratio r k) 0 ∧ (ratio r k 0)^2=1:=by
    intro k
    refine ⟨(hr k).div (hr 0) hne,?_⟩
    change (r k 0/r 0 0)^2=1
    rw [div_pow,hr0 k,hr0 0,div_self one_ne_zero]
  have heq:∀ᶠw in 𝓝 (0:ℂ),ratio r 0 w=1 ∧
      ∀k,(ratio r k w)^2=1+(b 0-b k)*(parameter r w)^2:=by
    filter_upwards [hunit,hrsq 0,hrsq 1,hrsq 2,hrsq 3] with w hn h0 h1 h2 h3
    have hall:∀k,r k w^2=1-b k*w^2:=by intro k;fin_cases k <;> assumption
    refine ⟨div_self hn,?_⟩
    intro k
    dsimp [ratio,parameter]
    rw [div_pow,div_pow]
    field_simp [hn]
    rw [hall k,h0]
    ring
  have hfinite:∀ᶠw in 𝓝[≠] (0:ℂ),parameter r w=(z 0 w)⁻¹ ∧
      ∀k,ratio r k w=z k w/z 0 w:=by
    filter_upwards [hrz 0,hrz 1,hrz 2,hrz 3,
      hunit.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w h0 h1 h2 h3 hn hw
    have hwn : w≠0 := by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hw
    have hall:∀k,r k w=w*z k w:=by intro k;fin_cases k <;> assumption
    have hz:z 0 w≠0:=by intro h;apply hn;rw [h0,h,mul_zero]
    constructor
    · dsimp [parameter]
      rw [h0]
      field_simp [hwn,hz]
    · intro k
      dsimp [ratio]
      rw [hall k,h0]
      field_simp [hwn,hz]
  exact ⟨r,inv,hr,hr0,hrz,hu,hu0,hud2,hi,hi0,hleft,hright,hratio,heq,hfinite⟩
end FourRootInfinityExtension318
