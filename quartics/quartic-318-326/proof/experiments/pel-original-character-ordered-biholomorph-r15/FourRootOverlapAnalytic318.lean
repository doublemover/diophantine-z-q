module
public import FourRootInfinityComplexCharts318
public import FourRootGluedTopology318
public section
noncomputable section
namespace FourRootOverlapAnalytic318
open Set Filter FourRootNormalizedPointCharts318 FourRootGluedTopology318
open scoped Topology
variable (b:Fin 4→ℂ)
local instance : TopologicalSpace (Completed b):=topology b

/-- Literal chart identification, retaining the actual nonzero root and
its three ratios. This is stronger than equality of the projected t. -/
lemma chart_identification (p:FinitePoints b) (q:InfinityPoints b) :
    finiteChart b p=infinityChart b q ↔
      ∃h:p.val.2 0≠0,(toInfinity b ⟨p,h⟩).val=q := by
  constructor
  · intro he
    have hq:q.val.1≠0:=by
      intro hz
      rw [infinityChart,dif_pos hz] at he
      cases he
    have hp:p=(toFinite b ⟨q,hq⟩).val:=
      Sum.inl.inj (he.trans (infinityChart_nonzero b q hq))
    have hn:p.val.2 0≠0:=hp.symm ▸ (toFinite b ⟨q,hq⟩).property
    refine ⟨hn,?_⟩
    have hpo:(⟨p,hn⟩:FiniteOverlap b)=toFinite b ⟨q,hq⟩:=Subtype.ext hp
    rw [hpo,toInfinity_toFinite]
  · rintro ⟨hp,rfl⟩
    exact (overlap_agreement b ⟨p,hp⟩).symm

@[expose] def forward (v:ℂ×(Fin 4→ℂ)):ℂ×(Fin 4→ℂ):=
  ((v.2 0)⁻¹,fun k=>v.2 k/v.2 0)
@[expose] def backward (v:ℂ×(Fin 4→ℂ)):ℂ×(Fin 4→ℂ):=
  (b 0+(v.1^2)⁻¹,fun k=>v.2 k/v.1)
lemma toInfinity_value (p:FiniteOverlap b):(toInfinity b p).val.val=forward p.val.val:=rfl
lemma toFinite_value (p:InfinityOverlap b):(toFinite b p).val.val=backward b p.val.val:=rfl

lemma root_analytic (k:Fin 4) (v:ℂ×(Fin 4→ℂ)):
    AnalyticAt ℂ (fun q:ℂ×(Fin 4→ℂ)=>q.2 k) v:=by
  have hproj : AnalyticAt ℂ (fun w:Fin 4→ℂ=>w k) v.2 :=
    (ContinuousLinearMap.proj k : (Fin 4→ℂ)→L[ℂ]ℂ).analyticAt v.2
  exact hproj.comp (analyticAt_snd : AnalyticAt ℂ (fun p:ℂ×(Fin 4→ℂ)=>p.2) v)
lemma forward_analytic (v:ℂ×(Fin 4→ℂ)) (hv:v.2 0≠0):
    AnalyticAt ℂ forward v:=
  ((root_analytic 0 v).inv hv).prod
    (AnalyticAt.pi (fun k=>(root_analytic k v).div (root_analytic 0 v) hv))
lemma backward_analytic (v:ℂ×(Fin 4→ℂ)) (hv:v.1≠0):
    AnalyticAt ℂ (backward b) v:=
  (analyticAt_const.add ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 hv))).prod
    (AnalyticAt.pi (fun k=>(root_analytic k v).div analyticAt_fst hv))
end FourRootOverlapAnalytic318
