module
public import FourRootFiniteComplexAtlas318
public section
noncomputable section
namespace FourRootInfinityComplexCharts318
open Set Filter FourRootNormalizedPointCharts318 FourRootInfinityGraph318
open scoped Topology Manifold ContDiff
variable (b:Fin 4→ℂ)

/-- Independent u-chart at each of the eight actual infinity points.
Finite points outside these local domains are covered by finite charts. -/
theorem exists_infinity_chart (s:InfinitySigns):
    ∃e:OpenPartialHomeomorph (InfinityPoints b) ℂ,center b s∈e.source ∧
      (∀q,e q=q.val.1) ∧
      AnalyticOnNhd ℂ (fun z=>(e.symm z).val) e.target := by
  obtain ⟨Z,hZ0,hbase,hroots,hright⟩:=parametrization b s
  have hA:AnalyticAt ℂ (fun z=>(Z z).val) 0:=by
    have ht:AnalyticAt ℂ (fun z=>(Z z).val.1) 0:=by
      simpa only [show (fun z=>(Z z).val.1)=id from funext hbase] using
        (analyticAt_id : AnalyticAt ℂ (fun z:ℂ=>z) 0)
    exact ht.prod (AnalyticAt.pi hroots)
  exact AnalyticEmbeddedCurveChart318.exists_chart
    {q:ℂ×(Fin 4→ℂ)|q.2 0=1 ∧ ∀k,q.2 k^2=1+(b 0-b k)*q.1^2}
    (center b s) Prod.fst continuous_fst Z hA hZ0 hbase hright

@[expose] def chart (s:InfinitySigns):OpenPartialHomeomorph (InfinityPoints b) ℂ:=
  (exists_infinity_chart b s).choose
lemma chart_center (s:InfinitySigns):center b s∈(chart b s).source:=
  (exists_infinity_chart b s).choose_spec.1
lemma chart_axis (s:InfinitySigns) (q:InfinityPoints b):chart b s q=q.val.1:=
  (exists_infinity_chart b s).choose_spec.2.1 q
lemma inverse_analytic (s:InfinitySigns):
    AnalyticOnNhd ℂ (fun z=>((chart b s).symm z).val) (chart b s).target:=
  (exists_infinity_chart b s).choose_spec.2.2

theorem analytic_transition (s t:InfinitySigns):
    AnalyticOnNhd ℂ ((chart b s).symm.trans (chart b t))
      ((chart b s).symm.trans (chart b t)).source:=by
  intro z hz
  change AnalyticAt ℂ (fun w=>chart b t ((chart b s).symm w)) z
  simp_rw [chart_axis]
  exact analyticAt_fst.comp (inverse_analytic b s z hz.1)
end FourRootInfinityComplexCharts318
