module
public import FourRootRegularGraph318
public section
noncomputable section
namespace FourRootInfinityGraph318
open Set Filter
open scoped Topology
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (s:InfinitySigns)
@[expose] def center : InfinityPoints b:=
  ⟨(0,s.val),s.property.1,by intro k;simpa using s.property.2 k⟩
lemma sign_ne (k:Fin 4) : s.val k≠0:=by
  intro h
  have hh:=s.property.2 k
  rw [h,zero_pow (by decide:2≠0)] at hh
  norm_num at hh

/-- All eight actual sign triples have independent unramified u-charts
on the normalized infinity space. The normalization s0=1 is retained on
EVERY point of the parametrization, not merely at its center. -/
theorem parametrization : ∃Z:ℂ→InfinityPoints b,
    Z 0=center b s ∧ (∀u,(Z u).val.1=u) ∧
    (∀k,AnalyticAt ℂ (fun u=>(Z u).val.2 k) 0) ∧
    (∀ᶠq in 𝓝 (center b s).val,
      (q.2 0=1 ∧ ∀k,q.2 k^2=1+(b 0-b k)*q.1^2)→(Z q.1).val=q) := by
  have hh:∀k:Fin 4,∃g:ℂ→ℂ,AnalyticAt ℂ g 0 ∧ g 0=s.val k ∧
      (∀u,g u^2=1+(b 0-b k)*u^2) ∧
      (k=0→∀u,g u=1) ∧
      ∀ᶠq in 𝓝 (center b s).val,
        (q.2 0=1 ∧ q.2 k^2=1+(b 0-b k)*q.1^2)→q.2 k=g q.1:=by
    intro k
    by_cases hk:k=0
    · subst k
      refine ⟨fun _=>1,analyticAt_const,s.property.1.symm,?_,fun _ _=>rfl,?_⟩
      · intro u;simp
      · exact Filter.Eventually.of_forall (fun _ h=>h.1)
    · have hf:AnalyticAt ℂ (fun u:ℂ=>1+(b 0-b k)*u^2) 0:=
        analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2))
      obtain ⟨g,hg,hg0,hgs,hgu⟩:=SquareRootAmbientGraph318.exists_graph
        (fun u:ℂ=>1+(b 0-b k)*u^2) 0 (s.val k) hf (sign_ne s k)
        (by simpa using s.property.2 k)
      refine ⟨g,hg,hg0,hgs,fun h=>False.elim (hk h),?_⟩
      have hc:ContinuousAt (fun q:ℂ×(Fin 4→ℂ)=>(q.1,q.2 k)) (center b s).val:=
        continuousAt_fst.prodMk ((continuous_apply k).continuousAt.comp continuousAt_snd)
      exact (hc.eventually hgu).mono (fun q h he=>h he.2)
  choose g hg hg0 hgs hgzero hgu using hh
  let Z:ℂ→InfinityPoints b:=fun u=>⟨(u,fun k=>g k u),hgzero 0 rfl u,fun k=>hgs k u⟩
  refine ⟨Z,Subtype.ext (Prod.ext rfl (funext hg0)),fun _=>rfl,hg,?_⟩
  filter_upwards [hgu 0,hgu 1,hgu 2,hgu 3] with q h0 h1 h2 h3
  intro he
  change (q.1,fun k=>g k q.1)=q
  apply Prod.ext
  · rfl
  · funext k
    fin_cases k
    · exact (h0 ⟨he.1,he.2 0⟩).symm
    · exact (h1 ⟨he.1,he.2 1⟩).symm
    · exact (h2 ⟨he.1,he.2 2⟩).symm
    · exact (h3 ⟨he.1,he.2 3⟩).symm
end FourRootInfinityGraph318
