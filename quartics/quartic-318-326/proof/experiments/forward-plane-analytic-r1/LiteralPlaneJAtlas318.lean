module
public import LiteralPlaneComparison318
public import LiteralThreePlaneGraph318
public section
noncomputable section
open Filter Set Topology
open scoped Manifold ContDiff
namespace LiteralPlaneJAtlas318
open LiteralThreePlanePoints318 LiteralPlaneComparison318 LiteralThreePlaneGraph318
set_option maxHeartbeats 400000

/-- The existing literal-plane projection is a local homeomorphism. This is
only a topological input: its analytic meaning is proved below using the
independently constructed quartic graph. The fixed localization parameter 1
is used solely to obtain the existing topological comparison. -/
theorem planeJ_localHomeomorph : IsLocalHomeomorph planeJ := by
  have h := AdmissibleJLocalHomeomorph318.sourceJ_localHomeomorph.comp
    (comparison 1).symm.isLocalHomeomorph
  simpa only [Function.comp_def,comparison_symm_j] using h

/-- Actual literal-j charts on the existing plane topology. -/
@[expose] def localChart (p : Plane) : OpenPartialHomeomorph Plane ℂ :=
  (planeJ_localHomeomorph.localInverseAt p).symm

lemma localChart_apply (p q : Plane) : localChart p q=planeJ q :=
  congrFun (planeJ_localHomeomorph.localInverseAt_symm p) q

lemma localChart_center (p : Plane) : p∈(localChart p).source :=
  planeJ_localHomeomorph.self_mem_localInverseAt_target

lemma transition_eq (a b : Plane) (z : ℂ) (hz : z∈(localChart a).target) :
    localChart b ((localChart a).symm z)=z := by
  rw [localChart_apply,←localChart_apply a ((localChart a).symm z)]
  exact (localChart a).right_inv hz

theorem analytic_transition (a b : Plane) :
    AnalyticOnNhd ℂ ((localChart a).symm.trans (localChart b))
      ((localChart a).symm.trans (localChart b)).source := by
  intro z hz
  apply analyticAt_id.congr
  filter_upwards [(localChart a).open_target.mem_nhds hz.1] with w hw
  exact (transition_eq a b w hw).symm

@[expose, instance_reducible] def complexChartedSpace : ChartedSpace ℂ Plane where
  atlas := Set.range localChart
  chartAt p := localChart p
  mem_chart_source := localChart_center
  chart_mem_atlas p := ⟨p,rfl⟩

theorem complex_manifold : letI:=complexChartedSpace; IsManifold 𝓘(ℂ) ω Plane := by
  letI:=complexChartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition a b).contDiffOn
      ((localChart a).symm.trans (localChart b)).open_source.uniqueDiffOn

/-- The literal ambient inclusion, retaining both coordinates. -/
@[expose] def coordinates (p : Plane) : ℂ × ℂ := (planeJ p,planeX p)

lemma coordinates_continuous : Continuous coordinates := by
  change Continuous (fun p : Plane => (p.val.1.val,p.val.2))
  fun_prop

/-- The actual chosen chart inverse agrees near its center with the independent
holomorphic graph of the literal quartic. This supplies the ambient analytic
content which does not follow merely from topological transport. -/
theorem inverse_coordinates_germ (p : Plane) :
    (fun z : ℂ => coordinates ((localChart p).symm z)) =ᶠ[𝓝 (planeJ p)]
      (fun z : ℂ => (z,graph p z)) := by
  have ht : Tendsto (localChart p).symm (𝓝 (planeJ p)) (𝓝 p) := by
    simpa only [localChart_apply] using
      (localChart p).tendsto_symm (localChart_center p)
  have hc : Tendsto (fun z : ℂ => coordinates ((localChart p).symm z))
      (𝓝 (planeJ p)) (𝓝 (coordinates p)) :=
    coordinates_continuous.continuousAt.tendsto.comp ht
  have hg := hc.eventually (graph_spec p).2.2.2
  have hj : ∀ᶠ z in 𝓝 (planeJ p), planeJ ((localChart p).symm z)=z := by
    simpa only [localChart_apply] using
      (localChart p).eventually_right_inverse' (localChart_center p)
  filter_upwards [hg,hj] with z hgz hjz
  apply Prod.ext
  · exact hjz
  · have hx := hgz.mp ((localChart p).symm z).property
    change planeX ((localChart p).symm z)=graph p z
    rw [←hjz]
    exact hx.symm

/-- The chart inverse has holomorphic literal ambient coordinates. -/
theorem inverse_coordinates_analytic (p : Plane) :
    AnalyticAt ℂ (fun z : ℂ => coordinates ((localChart p).symm z)) (planeJ p) := by
  exact (analyticAt_id.prod (graph_spec p).1).congr (inverse_coordinates_germ p).symm

end LiteralPlaneJAtlas318
