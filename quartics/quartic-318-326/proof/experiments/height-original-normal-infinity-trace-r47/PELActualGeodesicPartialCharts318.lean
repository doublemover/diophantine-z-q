module
public import PELActualSixGeodesicCharts318
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
namespace PELActualGeodesicPartialCharts318
open Set Filter
open scoped Topology
open PELActualSixGeodesicCharts318 PELActualEdgeHalfNeighborhood318
open PELMaximalActualComplexDomain318
set_option maxHeartbeats 2800000

/-- Full pole-free source and target of the SAME explicit rational chart.
This packages its genuine inverse, not a locally assumed chart. -/
@[expose] def source (i:Fin 6) : Set ℂ := {z | (rightEndpoint i:ℂ)-z≠0}
@[expose] def target (i:Fin 6) : Set ℂ := {w | 1+Complex.I*((orientation i:ℂ)*w)≠0}

theorem source_open (i:Fin 6) : IsOpen (source i) := isOpen_ne (by fun_prop) continuous_const
theorem target_open (i:Fin 6) : IsOpen (target i) := isOpen_ne (by fun_prop) continuous_const

theorem full_map_source (i:Fin 6) {z:ℂ} (hz:z∈source i) : straighten i z∈target i := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  change 1+Complex.I*((orientation i:ℂ)*straighten i z)≠0
  simp only [straighten,←mul_assoc,ho,one_mul]
  exact GeodesicCircleFlattening318.one_add_flatten_ne _ _ (endpoints_ordered i) _ hz

theorem full_map_target (i:Fin 6) {w:ℂ} (hw:w∈target i) : unstraighten i w∈source i :=
  GeodesicCircleFlattening318.endpoint_ne_unflatten _ _ (endpoints_ordered i) _ hw

theorem full_left_inverse (i:Fin 6) {z:ℂ} (hz:z∈source i) : unstraighten i (straighten i z)=z := by
  have ho:(orientation i:ℂ)*(orientation i:ℂ)=1 := by exact_mod_cast orientation_sq i
  simp only [unstraighten,straighten,←mul_assoc,ho,one_mul]
  exact GeodesicCircleFlattening318.unflatten_flatten _ _ (endpoints_ordered i) _ hz

theorem full_differentiable (i:Fin 6) {z:ℂ} (hz:z∈source i) : DifferentiableAt ℂ (straighten i) z := by
  unfold straighten GeodesicCircleFlattening318.flatten
  exact differentiableAt_const.mul (differentiableAt_const.mul
    ((differentiableAt_id.sub_const _).div (differentiableAt_const.sub differentiableAt_id) hz))

@[expose] def chart (i:Fin 6) : OpenPartialHomeomorph ℂ ℂ where
  toFun := straighten i
  invFun := unstraighten i
  source := source i
  target := target i
  map_source' := full_map_source i
  map_target' := full_map_target i
  left_inv' := full_left_inverse i
  right_inv' := fun _ hw=>straighten_unstraighten i _ hw
  open_source := source_open i
  open_target := target_open i
  continuousOn_toFun := fun _ hz=>(full_differentiable i hz).continuousAt.continuousWithinAt
  continuousOn_invFun := fun _ hw=>(unstraighten_differentiableAt i _ hw).continuousAt.continuousWithinAt

theorem chart_holomorphic (i:Fin 6) :
    AnalyticOnNhd ℂ (chart i) (chart i).source ∧
    AnalyticOnNhd ℂ (chart i).symm (chart i).target := by
  constructor
  · have hd : DifferentiableOn ℂ (chart i) (source i) :=
      fun z hz=>(full_differentiable i hz).differentiableWithinAt
    exact hd.analyticOnNhd (source_open i)
  · have hd : DifferentiableOn ℂ (chart i).symm (target i) :=
      fun z hz=>(unstraighten_differentiableAt i z hz).differentiableWithinAt
    exact hd.analyticOnNhd (target_open i)

/-- The actual regular-edge chart has its center on the real seam and
identifies its upper side with the original interior in a neighborhood. -/
theorem regular_chart {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    z∈(chart i).source ∧ ((chart i) z).im=0 ∧
    ∀ᶠw in 𝓝 ((chart i) z),((chart i).symm w∈openDomain ↔ 0<w.im) := by
  refine ⟨GeodesicCircleFlattening318.endpoint_ne _ _ hz.1,
    (straighten_real_iff i z hz.1).mpr hz.2.1,?_⟩
  exact (actual_regular_edge_inverse_halfchart hz).2.2
end PELActualGeodesicPartialCharts318
