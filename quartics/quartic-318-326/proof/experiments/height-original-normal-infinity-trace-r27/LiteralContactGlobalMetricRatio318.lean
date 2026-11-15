module
public import LiteralChartMetricFunctions318
public import OriginalUniformizedCurveAtlas318
public section
noncomputable section
namespace LiteralContactGlobalMetricRatio318
open Set Filter FourRootNormalizedPointCharts318 LiteralMetricExtension318
open LiteralContactMetricCharts318 LiteralChartMetricFunctions318
open PELUnlevelledComplexBase318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (H : UnlevelledBase ≃ₜ Completed contacts)
  (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
  (hI : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)

@[expose] def ratio (p : Completed contacts) : ℝ :=
  value (data p).kind 0 /
    (12540153541944538512*OriginalUniformizedCurveAtlas318.coefficient H (data p).chart p)

lemma regular_axis_eval (q : Completed contacts) (hq : Regular q)
    (x : Completed contacts) (hx : Regular x) : (data q).chart x=base x := by
  cases x with
  | inl x => exact (data q).regular_axis hq x
  | inr _ => exact hx.elim

include hH hI in
lemma ratio_positive (p : Completed contacts) : 0<ratio H p :=
  div_pos (value_positive (data p).kind)
    (mul_pos (by norm_num) (OriginalUniformizedCurveAtlas318.coefficient_positive H hH hI
      (data p).chart p (data p).mem (data p).maximal))

include hH hI in
/-- The globally selected ratio equals the actual local metric quotient
on an ENTIRE neighborhood in each produced source chart. Nearby regular
points are compared through their true t charts and the actual Poincare
transition law; the center equality is literal. No global metric-ratio
compatibility is supplied as an assumption. -/
theorem ratio_chart (p : Completed contacts) :
    ∀ᶠ z in 𝓝 (0 : ℂ),ratio H ((data p).chart.symm ((data p).chart p+z))=
      value (data p).kind z /
        (12540153541944538512*OriginalUniformizedCurveAtlas318.coefficient H (data p).chart
          ((data p).chart.symm ((data p).chart p+z))) := by
  let D := data p
  let E := D.chart
  obtain ⟨U,hU,hUo,hU0⟩ := eventually_nhds_iff.mp D.punctured
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ),E p+z∈E.target :=
    (continuousAt_const.add continuousAt_id).eventually
      (by simpa only [add_zero] using E.open_target.mem_nhds (E.map_source D.mem))
  filter_upwards [hUo.mem_nhds hU0,hn] with z hz hzt
  by_cases hz0 : z=0
  · subst z
    simp only [add_zero,E.left_inv D.mem]
    rfl
  let q := E.symm (E p+z)
  have hqe : q∈E.source := E.map_target hzt
  have heq : E q=E p+z := E.right_inv hzt
  have hq : Regular q := (hU z hz hz0).1
  have hbase : base q=coordinate D.kind z := (hU z hz hz0).2
  let T := (data q).chart
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ),z+w∈U ∧ z+w≠0 := by
    have hc : ContinuousAt (fun w : ℂ => z+w) 0 := continuousAt_const.add continuousAt_id
    exact (hc.eventually (by simpa only [add_zero] using hUo.mem_nhds hz)).and
      (hc.eventually (by simpa only [add_zero] using eventually_ne_nhds hz0))
  have hevent : (fun w : ℂ => T (E.symm (E q+w))-T q)=ᶠ[𝓝 (0:ℂ)]
      (fun w => coordinate D.kind (z+w)-coordinate D.kind z) := by
    filter_upwards [hnear] with w hw
    have hx := hU (z+w) hw.1 hw.2
    rw [heq,add_assoc]
    rw [regular_axis_eval q hq _ hx.1,regular_axis_eval q hq q hq,hx.2,hbase]
  have hf : DifferentiableAt ℂ (coordinate D.kind) (z+(0:ℂ)) := by
    simpa only [add_zero] using coordinate_differentiable D.kind z hz0
  have hd := (hf.hasDerivAt.comp 0
    ((hasDerivAt_const 0 z).add (hasDerivAt_id 0))).sub_const (coordinate D.kind z)
  have hder : deriv (fun w : ℂ => T (E.symm (E q+w))-T q) 0=
      deriv (coordinate D.kind) z := by
    rw [hevent.deriv_eq]
    simpa only [add_zero,zero_add,mul_one] using hd.deriv
  have ht := OriginalUniformizedCurveAtlas318.coefficient_transition H hH hI E T q
    hqe (data q).mem D.maximal (data q).maximal
  rw [hder] at ht
  have hpe := OriginalUniformizedCurveAtlas318.coefficient_positive H hH hI E q hqe D.maximal
  have hpt := OriginalUniformizedCurveAtlas318.coefficient_positive H hH hI T q (data q).mem (data q).maximal
  have hdn : ‖deriv (coordinate D.kind) z‖^2≠0 := by
    intro hz
    rw [hz,mul_zero] at ht
    exact hpe.ne' ht
  obtain ⟨hqoff,hkind⟩ := (data q).regular_kind hq
  change ratio H q=value D.kind z/(12540153541944538512*OriginalUniformizedCurveAtlas318.coefficient H E q)
  rw [ratio,hkind]
  change MetricPullback318.sourceCoefficient contacts (base q+0)/
      (12540153541944538512*OriginalUniformizedCurveAtlas318.coefficient H T q)=_
  rw [add_zero,hbase,value_pullback D.kind z hz0,ht]
  field_simp [hpt.ne',hdn]
  <;> ring
end LiteralContactGlobalMetricRatio318
