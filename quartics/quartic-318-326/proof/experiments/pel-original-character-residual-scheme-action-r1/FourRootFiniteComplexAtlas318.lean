module
public import AnalyticEmbeddedCurveChart318
public import FourRootInfinityGraph318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
namespace FourRootFiniteComplexAtlas318
open Set Filter FourRootNormalizedPointCharts318
open scoped Topology Manifold ContDiff
variable (b:Fin 4→ℂ) (hb:Function.Injective b)

@[expose] def axis : Option (Fin 4)→(ℂ×(Fin 4→ℂ))→ℂ
  | none=>Prod.fst
  | some k=>fun p=>p.2 k
lemma axis_continuous (j:Option (Fin 4)) : Continuous (axis j):=by
  cases j with
  | none=>exact continuous_fst
  | some k=>exact (continuous_apply k).comp continuous_snd
lemma axis_analytic (j:Option (Fin 4)) (v:ℂ×(Fin 4→ℂ)) :
    AnalyticAt ℂ (axis j) v:=by
  cases j with
  | none=>exact analyticAt_fst
  | some k=>exact ((ContinuousLinearMap.proj (R:=ℂ) k).analyticAt _).comp analyticAt_snd

/-- Every finite point has an independent chart: t off all branch fibers,
or the exact vanishing root at a branch. Distinct branches make the other
three roots units, so no simultaneous singular branch is silently allowed. -/
theorem exists_finite_chart (p:FinitePoints b) :
    ∃e:OpenPartialHomeomorph (FinitePoints b) ℂ,p∈e.source ∧
      (∃j:Option (Fin 4),∀q,e q=axis j q.val) ∧
      AnalyticOnNhd ℂ (fun z=>(e.symm z).val) e.target := by
  by_cases hp:∀k,p.val.2 k≠0
  · obtain ⟨Z,hZ0,hbase,hroots,hright⟩:=FourRootRegularGraph318.parametrization b p hp
    have hA:AnalyticAt ℂ (fun z=>(Z z).val) p.val.1:=by
      have ht:AnalyticAt ℂ (fun z=>(Z z).val.1) p.val.1:=by
        simpa only [show (fun z=>(Z z).val.1)=id from funext hbase] using
          (analyticAt_id : AnalyticAt ℂ (fun z:ℂ=>z) p.val.1)
      exact ht.prod (AnalyticAt.pi hroots)
    obtain ⟨e,he,ha,hi⟩:=AnalyticEmbeddedCurveChart318.exists_chart
      {q:ℂ×(Fin 4→ℂ)|∀k,q.2 k^2=q.1-b k} p
      (axis none) (axis_continuous none) Z hA hZ0 hbase hright
    exact ⟨e,he,⟨none,ha⟩,hi⟩
  · push_neg at hp
    obtain ⟨j,hj⟩:=hp
    have ht:p.val.1=b j:=by
      have hh:=p.property j
      rw [hj,zero_pow (by decide:2≠0)] at hh
      exact sub_eq_zero.mp hh.symm
    obtain ⟨Z,hZ0,hbase,hroot,hroots,hright⟩:=
      FourRootFiniteBranchGraph318.parametrization b hb j p ht
    have hA:AnalyticAt ℂ (fun z=>(Z z).val) 0:=by
      have ha:AnalyticAt ℂ (fun z=>(Z z).val.1) 0:=by
        rw [show (fun z=>(Z z).val.1)=(fun z=>b j+z^2) from funext hbase]
        exact analyticAt_const.add (analyticAt_id.pow 2)
      exact ha.prod (AnalyticAt.pi hroots)
    obtain ⟨e,he,ha,hi⟩:=AnalyticEmbeddedCurveChart318.exists_chart
      {q:ℂ×(Fin 4→ℂ)|∀k,q.2 k^2=q.1-b k} p
      (axis (some j)) (axis_continuous (some j)) Z
      (by simpa only [axis,hj] using hA)
      (by simpa only [axis,hj] using hZ0) hroot hright
    exact ⟨e,he,⟨some j,ha⟩,hi⟩

@[expose] def chart (p:FinitePoints b):OpenPartialHomeomorph (FinitePoints b) ℂ:=
  (exists_finite_chart b hb p).choose
lemma chart_center (p:FinitePoints b):p∈(chart b hb p).source:=
  (exists_finite_chart b hb p).choose_spec.1
lemma chart_axis (p:FinitePoints b):∃j:Option (Fin 4),∀q,chart b hb p q=axis j q.val:=
  (exists_finite_chart b hb p).choose_spec.2.1
lemma inverse_analytic (p:FinitePoints b):
    AnalyticOnNhd ℂ (fun z=>((chart b hb p).symm z).val) (chart b hb p).target:=
  (exists_finite_chart b hb p).choose_spec.2.2

theorem analytic_transition (p q:FinitePoints b):
    AnalyticOnNhd ℂ ((chart b hb p).symm.trans (chart b hb q))
      ((chart b hb p).symm.trans (chart b hb q)).source:=by
  intro z hz
  obtain ⟨j,hj⟩:=chart_axis b hb q
  have he:(fun w=>chart b hb q ((chart b hb p).symm w))=
      fun w=>axis j ((chart b hb p).symm w).val:=funext (fun w=>hj _)
  change AnalyticAt ℂ (fun w=>chart b hb q ((chart b hb p).symm w)) z
  rw [he]
  exact (axis_analytic j _).comp (inverse_analytic b hb p z hz.1)

@[expose,instance_reducible] def chartedSpace:ChartedSpace ℂ (FinitePoints b) where
  atlas:=Set.range (chart b hb)
  chartAt:=chart b hb
  mem_chart_source:=chart_center b hb
  chart_mem_atlas p:=⟨p,rfl⟩
theorem complex_manifold : letI:=chartedSpace b hb; IsManifold 𝓘(ℂ,ℂ) ω (FinitePoints b):=by
  letI:=chartedSpace b hb
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition b hb p q).contDiffOn
      ((chart b hb p).symm.trans (chart b hb q)).open_source.uniqueDiffOn
end FourRootFiniteComplexAtlas318
