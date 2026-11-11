module
public import FourRootFiniteBranchGraph318
public section
noncomputable section
namespace FourRootRegularGraph318
open Set Filter
open scoped Topology
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (p:FinitePoints b) (hp:∀k,p.val.2 k≠0)

/-- The original t-coordinate is a true parameter wherever every root is
nonzero. The four signed local roots are prescribed by the actual point. -/
theorem parametrization : ∃Z:ℂ→FinitePoints b,
    Z p.val.1=p ∧ (∀t,(Z t).val.1=t) ∧
    (∀k,AnalyticAt ℂ (fun t=>(Z t).val.2 k) p.val.1) ∧
    (∀ᶠq in 𝓝 p.val,(∀k,q.2 k^2=q.1-b k)→(Z q.1).val=q) := by
  have hh:∀k:Fin 4,∃g:ℂ→ℂ,AnalyticAt ℂ g p.val.1 ∧
      g p.val.1=p.val.2 k ∧ (∀t,g t^2=t-b k) ∧
      ∀ᶠq in 𝓝 p.val,q.2 k^2=q.1-b k→q.2 k=g q.1:=by
    intro k
    obtain ⟨g,hg,hg0,hgs,hgu⟩:=SquareRootAmbientGraph318.exists_graph
      (fun t=>t-b k) p.val.1 (p.val.2 k) (analyticAt_id.sub analyticAt_const)
      (hp k) (p.property k)
    refine ⟨g,hg,hg0,hgs,?_⟩
    exact (continuousAt_fst.prodMk
      ((continuous_apply k).continuousAt.comp continuousAt_snd)).eventually hgu
  choose g hg hg0 hgs hgu using hh
  let Z:ℂ→FinitePoints b:=fun t=>⟨(t,fun k=>g k t),fun k=>hgs k t⟩
  refine ⟨Z,?_,fun _=>rfl,hg,?_⟩
  · apply Subtype.ext
    exact Prod.ext rfl (funext hg0)
  · filter_upwards [hgu 0,hgu 1,hgu 2,hgu 3] with q h0 h1 h2 h3
    intro he
    apply Prod.ext rfl
    funext k
    fin_cases k
    · exact (h0 (he 0)).symm
    · exact (h1 (he 1)).symm
    · exact (h2 (he 2)).symm
    · exact (h3 (he 3)).symm
end FourRootRegularGraph318
