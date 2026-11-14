module
public import FourRootOverlapAnalytic318
public section
noncomputable section
namespace FourRootCompletedComplexAtlas318
open Set Filter FourRootNormalizedPointCharts318 FourRootGluedTopology318
open FourRootOverlapAnalytic318
open scoped Topology Manifold ContDiff
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance : TopologicalSpace (Completed b):=topology b

@[expose] def finiteChart (p:FinitePoints b):OpenPartialHomeomorph (Completed b) ℂ:=
  (FourRootFiniteComplexAtlas318.chart b hb p).lift_openEmbedding (finite_openEmbedding b)
@[expose] def infinityChart (s:InfinitySigns):OpenPartialHomeomorph (Completed b) ℂ:=
  (FourRootInfinityComplexCharts318.chart b s).lift_openEmbedding (infinity_openEmbedding b)
lemma finite_inverse (p:FinitePoints b) (z:ℂ):
    (finiteChart b hb p).symm z=FourRootNormalizedPointCharts318.finiteChart b
      ((FourRootFiniteComplexAtlas318.chart b hb p).symm z):=rfl
lemma infinity_inverse (s:InfinitySigns) (z:ℂ):
    (infinityChart b s).symm z=FourRootNormalizedPointCharts318.infinityChart b
      ((FourRootInfinityComplexCharts318.chart b s).symm z):=rfl
lemma finite_apply (p q:FinitePoints b):
    finiteChart b hb p (FourRootNormalizedPointCharts318.finiteChart b q)=
      FourRootFiniteComplexAtlas318.chart b hb p q:=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _
lemma infinity_apply (s:InfinitySigns) (q:InfinityPoints b):
    infinityChart b s (FourRootNormalizedPointCharts318.infinityChart b q)=
      FourRootInfinityComplexCharts318.chart b s q:=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

lemma finite_to_infinity_denominator (p:FinitePoints b) (s:InfinitySigns) (z:ℂ)
    (hz:z∈((finiteChart b hb p).symm.trans (infinityChart b s)).source):
    ((FourRootFiniteComplexAtlas318.chart b hb p).symm z).val.2 0≠0:=by
  obtain ⟨q,hq,he⟩:=hz.2
  obtain ⟨hn,_⟩:=(chart_identification b _ q).mp he.symm
  exact hn
lemma infinity_to_finite_denominator (s:InfinitySigns) (p:FinitePoints b) (z:ℂ)
    (hz:z∈((infinityChart b s).symm.trans (finiteChart b hb p)).source):
    ((FourRootInfinityComplexCharts318.chart b s).symm z).val.1≠0:=by
  obtain ⟨q,hq,he⟩:=hz.2
  obtain ⟨hn,hv⟩:=(chart_identification b q _).mp he
  change (toInfinity b ⟨q,hn⟩).val =
    (FourRootInfinityComplexCharts318.chart b s).symm z at hv
  rw [←hv]
  exact inv_ne_zero hn

lemma finite_to_infinity_value (p:FinitePoints b) (s:InfinitySigns) (z:ℂ)
    (hz:((FourRootFiniteComplexAtlas318.chart b hb p).symm z).val.2 0≠0):
    infinityChart b s ((finiteChart b hb p).symm z)=
      FourRootInfinityComplexCharts318.chart b s
        (toInfinity b ⟨(FourRootFiniteComplexAtlas318.chart b hb p).symm z,hz⟩).val:=by
  rw [finite_inverse,←overlap_agreement b
    ⟨(FourRootFiniteComplexAtlas318.chart b hb p).symm z,hz⟩,infinity_apply]
lemma infinity_to_finite_value (s:InfinitySigns) (p:FinitePoints b) (z:ℂ)
    (hz:((FourRootInfinityComplexCharts318.chart b s).symm z).val.1≠0):
    finiteChart b hb p ((infinityChart b s).symm z)=
      FourRootFiniteComplexAtlas318.chart b hb p
        (toFinite b ⟨(FourRootInfinityComplexCharts318.chart b s).symm z,hz⟩).val:=by
  rw [infinity_inverse,infinityChart_nonzero b _ hz]
  exact finite_apply b hb p _

/-- The mixed transition is exactly u=1/z0. No analytic structure from
the original PEL source is used to prove it holomorphic. -/
theorem finite_to_infinity_analytic (p:FinitePoints b) (s:InfinitySigns):
    AnalyticOnNhd ℂ ((finiteChart b hb p).symm.trans (infinityChart b s))
      ((finiteChart b hb p).symm.trans (infinityChart b s)).source:=by
  intro z hz
  have ha:=FourRootFiniteComplexAtlas318.inverse_analytic b hb p z hz.1
  have hd:=finite_to_infinity_denominator b hb p s z hz
  have hu:AnalyticAt ℂ (fun w=>
      ((FourRootFiniteComplexAtlas318.chart b hb p).symm w).val.2 0) z:=
    (root_analytic 0 _).comp ha
  have hn:=hu.continuousAt.eventually (eventually_ne_nhds hd)
  apply (hu.inv hd).congr
  filter_upwards [hn] with w hw
  change _=infinityChart b s ((finiteChart b hb p).symm w)
  rw [finite_to_infinity_value b hb p s w hw,FourRootInfinityComplexCharts318.chart_axis]
  rfl

/-- The reverse mixed transition uses the true t=b0+u^-2 or s_k/u,
according to the independent finite chart's actual coordinate axis. -/
theorem infinity_to_finite_analytic (s:InfinitySigns) (p:FinitePoints b):
    AnalyticOnNhd ℂ ((infinityChart b s).symm.trans (finiteChart b hb p))
      ((infinityChart b s).symm.trans (finiteChart b hb p)).source:=by
  intro z hz
  have ha:=FourRootInfinityComplexCharts318.inverse_analytic b s z hz.1
  have hd:=infinity_to_finite_denominator b hb s p z hz
  have hn:=(analyticAt_fst.comp ha).continuousAt.eventually (eventually_ne_nhds hd)
  obtain ⟨j,hj⟩:=FourRootFiniteComplexAtlas318.chart_axis b hb p
  have hback:AnalyticAt ℂ (fun w:ℂ=>
      backward b ((FourRootInfinityComplexCharts318.chart b s).symm w).val) z:=
    (backward_analytic b _ hd).comp
      (f:=fun w:ℂ=>((FourRootInfinityComplexCharts318.chart b s).symm w).val) ha
  have hf:AnalyticAt ℂ (fun w=>FourRootFiniteComplexAtlas318.axis j
      (backward b ((FourRootInfinityComplexCharts318.chart b s).symm w).val)) z:=
    (FourRootFiniteComplexAtlas318.axis_analytic j _).comp
      (f:=fun w:ℂ=>backward b
        ((FourRootInfinityComplexCharts318.chart b s).symm w).val) hback
  apply hf.congr
  filter_upwards [hn] with w hw
  change _=finiteChart b hb p ((infinityChart b s).symm w)
  rw [infinity_to_finite_value b hb s p w hw,hj,toFinite_value]

@[expose] def localChart : FinitePoints b⊕InfinitySigns→OpenPartialHomeomorph (Completed b) ℂ:=
  Sum.elim (finiteChart b hb) (infinityChart b)
lemma covers (p:Completed b):∃i,p∈(localChart b hb i).source:=by
  rcases p with p|s
  · exact ⟨Sum.inl p,⟨p,FourRootFiniteComplexAtlas318.chart_center b hb p,rfl⟩⟩
  · exact ⟨Sum.inr s,⟨FourRootInfinityGraph318.center b s,
      FourRootInfinityComplexCharts318.chart_center b s,infinityChart_zero b s⟩⟩

theorem analytic_transition (i j:FinitePoints b⊕InfinitySigns):
    AnalyticOnNhd ℂ ((localChart b hb i).symm.trans (localChart b hb j))
      ((localChart b hb i).symm.trans (localChart b hb j)).source:=by
  cases i with
  | inl p=>
    cases j with
    | inl q=>
      simpa only [localChart,Sum.elim_inl,finiteChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using FourRootFiniteComplexAtlas318.analytic_transition b hb p q
    | inr s=>exact finite_to_infinity_analytic b hb p s
  | inr s=>
    cases j with
    | inl p=>exact infinity_to_finite_analytic b hb s p
    | inr t=>
      simpa only [localChart,Sum.elim_inr,infinityChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using FourRootInfinityComplexCharts318.analytic_transition b s t

@[expose,instance_reducible] def chartedSpace:ChartedSpace ℂ (Completed b) where
  atlas:=Set.range (localChart b hb)
  chartAt p:=localChart b hb (covers b hb p).choose
  mem_chart_source p:=(covers b hb p).choose_spec
  chart_mem_atlas p:=⟨_,rfl⟩

/-- Independent complex structure on the ACTUAL normalized four-root
completion, including every finite branch and all eight infinity points. -/
theorem complex_manifold : letI:=chartedSpace b hb; IsManifold 𝓘(ℂ,ℂ) ω (Completed b):=by
  letI:=chartedSpace b hb
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition b hb p q).contDiffOn
      ((localChart b hb p).symm.trans (localChart b hb q)).open_source.uniqueDiffOn
end FourRootCompletedComplexAtlas318
