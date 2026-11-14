module
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public section
noncomputable section
namespace EntireSimultaneousNonzero318
open Filter Topology Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Two nontrivial entire functions cannot have their zero loci cover
the whole complex vector space. This is the several-variable identity
principle on an OPEN neighborhood, not isolated zeros in dimension two. -/
theorem exists_product_ne_zero (f g:E→ℂ)
    (hf:AnalyticOnNhd ℂ f Set.univ) (hg:AnalyticOnNhd ℂ g Set.univ)
    (hfc:Continuous f) (hfn:∃p,f p≠0) (hgn:∃q,g q≠0):
    ∃a,f a*g a≠0:=by
  obtain ⟨p,hp⟩:=hfn
  obtain ⟨q,hq⟩:=hgn
  by_contra h
  push_neg at h
  have hn:∀ᶠa in 𝓝 p,f a≠0:=hfc.continuousAt.eventually_ne hp
  have hz:g=ᶠ[𝓝 p] 0:=by
    filter_upwards [hn] with a ha
    exact (mul_eq_zero.mp (h a)).resolve_left ha
  have he:=hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ p) hz
  exact hq (he (Set.mem_univ q))
/-- Entire functions on an arbitrary complex normed vector space are
handled on the actual affine complex line joining their two nonzero
witnesses. This uses the pinned one-variable holomorphic-to-analytic
bridge, and does not assume a missing several-variable analytic API. -/
theorem differentiable_exists_product_ne_zero (f g:E→ℂ)
    (hf:Differentiable ℂ f) (hg:Differentiable ℂ g)
    (hfn:∃p,f p≠0) (hgn:∃q,g q≠0):∃a,f a*g a≠0:=by
  obtain ⟨p,hp⟩:=hfn
  obtain ⟨q,hq⟩:=hgn
  let line:ℂ→E:=fun t=>p+t • (q-p)
  have hl:Differentiable ℂ line:=differentiable_const.add
    (differentiable_id.smul_const (q-p))
  have h0:line 0=p:=by simp [line]
  have h1:line 1=q:=by
    simp only [line,one_smul]
    abel
  obtain ⟨t,ht⟩:=exists_product_ne_zero (f∘line) (g∘line)
    ((hf.comp hl).differentiableOn.analyticOnNhd isOpen_univ)
    ((hg.comp hl).differentiableOn.analyticOnNhd isOpen_univ)
    (hf.comp hl).continuous ⟨0,by simpa only [Function.comp_apply,h0] using hp⟩
      ⟨1,by simpa only [Function.comp_apply,h1] using hq⟩
  exact ⟨line t,ht⟩
end EntireSimultaneousNonzero318
