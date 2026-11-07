module
public import HolomorphicPoincare318
public import GlobalSectionNorm318
public section
noncomputable section
open Filter Set SourceMetricCharts318 PeterssonSectionNorm318
open scoped Topology
namespace UniformizingSectionBounds318
set_option maxHeartbeats 0

/-- Genuine local uniformizing maps replace the hyperbolic curvature and
regularity fields. Only actual atlas/global metric realization remains. -/
structure Data (X:Type*) [TopologicalSpace X] where
  kind : X→Chart
  ratio : X→ℝ
  ratio_continuous : Continuous ratio
  ratio_positive : ∀x,0<ratio x
  chart : X→ℝ×ℝ→X
  chart_origin : ∀x,chart x (0,0)=x
  chart_continuous : ∀x,ContinuousAt (chart x) (0,0)
  uniformizer : X→ℂ→ℂ
  analytic : ∀x,AnalyticAt ℂ (uniformizer x) 0
  upper : ∀x,0<(uniformizer x 0).im
  noncritical : ∀x,deriv (uniformizer x) 0≠0
  ratio_chart : ∀x,(fun w=>ratio (chart x w))=ᶠ[𝓝 (0,0)]
    (fun w=>(kind x).coefficient w/
      (12540153541944538512*HolomorphicPoincare318.coefficient (uniformizer x) w))

variable {X:Type*} [TopologicalSpace X]

@[expose] def Data.toNormData (D:Data X) : GlobalSectionNorm318.Data X where
  kind := D.kind
  ratio := D.ratio
  ratio_continuous := D.ratio_continuous
  ratio_positive := D.ratio_positive
  chart := D.chart
  chart_origin := D.chart_origin
  chart_continuous := D.chart_continuous
  hyperbolic := fun x=>HolomorphicPoincare318.coefficient (D.uniformizer x)
  hyperbolic_smooth := fun x=>HolomorphicPoincare318.coefficient_axisC2 _ (D.analytic x) (D.upper x)
  hyperbolic_positive := fun x=>HolomorphicPoincare318.coefficient_positive _ (D.upper x) (D.noncritical x)
  ratio_chart := D.ratio_chart
  hyperbolic_curvature := fun x=>HolomorphicPoincare318.curvature_eq_neg_one _ (D.analytic x) (D.upper x) (D.noncritical x)

/-- The actual two section-norm bounds from geometric local uniformizers,
with no metric curvature, harmonicity, gradient or norm-estimate premise. -/
theorem Data.integral_section_norms [CompactSpace X] [Nonempty X] (D:Data X) (x:X) :
    quadraticNorm (HolomorphicPoincare318.coefficient (D.uniformizer x) (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section0 (D.kind x))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) ∧
    quadraticNorm (HolomorphicPoincare318.coefficient (D.uniformizer x) (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section1 (D.kind x))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) :=
  D.toNormData.integral_section_norms x

end UniformizingSectionBounds318
#print axioms UniformizingSectionBounds318.Data.integral_section_norms
