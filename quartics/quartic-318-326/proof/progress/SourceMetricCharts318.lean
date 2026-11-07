module
public import LiteralOriginCurvature318
public import ActualMetricComparison318
public section
noncomputable section
open Filter Set ConformalCurvature318 LiteralMetricExtension318 MetricSmoothExtension318
open QuadraticOrigin318
open scoped Topology
namespace SourceMetricCharts318
set_option maxHeartbeats 0

/-- These are the three actual source-coordinate types. Their realization as
charts of a geometric compact curve is intentionally not asserted here. -/
inductive Chart where
  | regular (z:ℂ) (offContact:∀i:Fin 4,z≠contacts i)
  | finiteBranch (i:Fin 4)
  | infinity

@[expose] def Chart.coefficient : Chart→(ℝ×ℝ)→ℝ
  | .regular z _ => fun w=>MetricPullback318.sourceCoefficient contacts (z+complexCoord w)
  | .finiteBranch i => fun w=>branchCoefficient
      (fun j:{j:Fin 4 // j≠i}=>contacts i-contacts j) (complexCoord w)
  | .infinity => fun w=>infinityCoefficient contacts (complexCoord w)

theorem Chart.smooth (c:Chart) : AxisC2 c.coefficient := by
  cases c with
  | regular z hz => exact LiteralCurvature318.literal_axisC2 z hz
  | finiteBranch i => exact finite_branch_axisC2 i
  | infinity => exact infinity_axisC2

theorem Chart.positive (c:Chart) : 0<c.coefficient (0,0) := by
  cases c with
  | regular z hz => simpa [Chart.coefficient,complexCoord] using LiteralCurvature318.literal_positive z hz
  | finiteBranch i => simpa [Chart.coefficient,complexCoord] using (finite_branch_extension i).2
  | infinity => simpa [Chart.coefficient,complexCoord] using infinity_extension.2.2

/-- Every chosen source chart has the same actual computed curvature bound,
including the branch and infinity origins. -/
theorem Chart.curvature_bound (c:Chart) :
    curvature c.coefficient≤-1/(12540153541944538512:ℝ) := by
  cases c with
  | regular z hz => simpa only [Chart.coefficient,complexCoord,neg_div,one_div] using LiteralCurvature318.literal_curvature_bound z hz
  | finiteBranch i => simpa only [Chart.coefficient,complexCoord,neg_div,one_div] using LiteralOriginCurvature318.finite_branch_curvature_bound i
  | infinity => simpa only [Chart.coefficient,complexCoord,neg_div,one_div] using LiteralOriginCurvature318.infinity_curvature_bound

/-- The source metric comparison no longer assumes source smoothness,
positivity or curvature. Actual geometric charts/global ratio and hyperbolic
metric realization remain the explicit geometric interface. -/
theorem metric_comparison {X:Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (kind:X→Chart) (ratio:X→ℝ) (hcontinuous:Continuous ratio) (hpositive:∀x,0<ratio x)
    (chart:X→ℝ×ℝ→X) (chart_origin:∀x,chart x (0,0)=x)
    (chart_continuous:∀x,ContinuousAt (chart x) (0,0))
    (hyperbolic:X→ℝ×ℝ→ℝ) (hyperbolic_smooth:∀x,AxisC2 (hyperbolic x))
    (hyperbolic_positive:∀x,0<hyperbolic x (0,0))
    (ratio_chart:∀x,(fun w=>ratio (chart x w))=ᶠ[𝓝 (0,0)]
      (fun w=>(kind x).coefficient w/(12540153541944538512*hyperbolic x w)))
    (hyperbolic_curvature:∀x,curvature (hyperbolic x)=-1) :
    ∀x,(kind x).coefficient (0,0)≤12540153541944538512*hyperbolic x (0,0) :=
  ActualMetricComparison318.metric_comparison ratio hcontinuous hpositive 12540153541944538512
    (by norm_num) chart chart_origin chart_continuous (fun x=>(kind x).coefficient) hyperbolic
    (fun x=>(kind x).smooth) hyperbolic_smooth (fun x=>(kind x).positive) hyperbolic_positive
    ratio_chart (fun x=>(kind x).curvature_bound) hyperbolic_curvature

end SourceMetricCharts318
#print axioms SourceMetricCharts318.Chart.curvature_bound
#print axioms SourceMetricCharts318.metric_comparison
