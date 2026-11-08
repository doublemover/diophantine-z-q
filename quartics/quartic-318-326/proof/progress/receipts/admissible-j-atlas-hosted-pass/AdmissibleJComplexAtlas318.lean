module
public import AdmissibleJLocalHomeomorph318
public import Mathlib.Geometry.Manifold.HasGroupoid
public section
noncomputable section
open Filter Set Topology
open scoped Manifold ContDiff
namespace AdmissibleJComplexAtlas318
open ThreeArithmeticQuotient318 AdmissibleJLocalHomeomorph318
set_option maxHeartbeats 0

/-- A chart of the actual admissible source whose forward coordinate is the
genuine j-function. The local inverse comes from the checked local homeomorphism. -/
@[expose] def localChart (q : Source) : OpenPartialHomeomorph Source ℂ :=
  (sourceJ_localHomeomorph.localInverseAt q).symm

lemma localChart_apply (q p : Source) : localChart q p=sourceComplexJ p :=
  congrFun (sourceJ_localHomeomorph.localInverseAt_symm q) p

lemma localChart_center (q : Source) : q∈(localChart q).source :=
  sourceJ_localHomeomorph.self_mem_localInverseAt_target

lemma transition_eq (a b : Source) (w : ℂ) (hw : w∈(localChart a).target) :
    localChart b ((localChart a).symm w)=w := by
  rw [localChart_apply,←localChart_apply a ((localChart a).symm w)]
  exact (localChart a).right_inv hw

/-- The actual local j charts have identity transition maps on each overlap,
so holomorphic compatibility is proved rather than assumed. -/
theorem analytic_transition (a b : Source) :
    AnalyticOnNhd ℂ ((localChart a).symm.trans (localChart b))
      ((localChart a).symm.trans (localChart b)).source := by
  intro w hw
  apply analyticAt_id.congr
  filter_upwards [(localChart a).open_target.mem_nhds hw.1] with z hz
  exact (transition_eq a b z hz).symm

@[expose, instance_reducible] def complexChartedSpace : ChartedSpace ℂ Source where
  atlas := Set.range localChart
  chartAt q := localChart q
  mem_chart_source := localChart_center
  chart_mem_atlas q := ⟨q,rfl⟩

/-- An actual complex analytic manifold on the existing admissible Gamma1(3)
source, constructed from genuine j local inverses and literal identity transitions. -/
theorem complex_manifold : letI:=complexChartedSpace; IsManifold 𝓘(ℂ) ω Source := by
  letI:=complexChartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition a b).contDiffOn
      ((localChart a).symm.trans (localChart b)).open_source.uniqueDiffOn

end AdmissibleJComplexAtlas318
