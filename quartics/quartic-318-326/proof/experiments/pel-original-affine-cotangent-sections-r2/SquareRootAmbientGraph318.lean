module
public import LocalHolomorphicSquareRoot318
public section
noncomputable section
namespace SquareRootAmbientGraph318
open Filter
open scoped Topology

/-- Prescribed nonzero root, with FULL ambient local uniqueness on the
actual square equation, not just an inverse on a parametrized subset. -/
theorem exists_graph (f:ℂ→ℂ) (a r:ℂ) (hf:AnalyticAt ℂ f a)
    (hr:r≠0) (hs:r^2=f a) :
    ∃g:ℂ→ℂ,AnalyticAt ℂ g a ∧ g a=r ∧ (∀t,g t^2=f t) ∧
      ∀ᶠp in 𝓝 ((a,r):ℂ×ℂ),p.2^2=f p.1 → p.2=g p.1 := by
  have hfa:f a≠0:=hs ▸ pow_ne_zero 2 hr
  obtain ⟨g,hg,hga,hgs⟩:=LocalHolomorphicSquareRoot318.exists_local_root f a r hf hfa hs
  refine ⟨g,hg,hga,hgs,?_⟩
  have hc:ContinuousAt (fun p:ℂ×ℂ=>p.2+g p.1) (a,r):=
    continuousAt_snd.add (hg.continuousAt.comp continuousAt_fst)
  have hn:(r+g a)≠0:=by rw [hga];exact add_self_ne_zero.mpr hr
  filter_upwards [hc.eventually_ne hn] with p hp he
  have hzero:(p.2-g p.1)*(p.2+g p.1)=0:=by
    linear_combination he-hgs p.1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hp)
end SquareRootAmbientGraph318
