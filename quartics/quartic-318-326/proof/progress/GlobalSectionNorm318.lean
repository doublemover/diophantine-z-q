module
public import PeterssonSectionNorm318
public section
noncomputable section
open Filter Set ConformalCurvature318 SourceMetricCharts318 PeterssonSectionNorm318
open scoped Topology
namespace GlobalSectionNorm318
set_option maxHeartbeats 0

/-- Concrete analytic data for the compact geometric realization. Neither a
source curvature bound nor a section-norm estimate is a field of this data. -/
structure Data (X:Type*) [TopologicalSpace X] where
  kind : X→Chart
  ratio : X→ℝ
  ratio_continuous : Continuous ratio
  ratio_positive : ∀x,0<ratio x
  chart : X→ℝ×ℝ→X
  chart_origin : ∀x,chart x (0,0)=x
  chart_continuous : ∀x,ContinuousAt (chart x) (0,0)
  hyperbolic : X→ℝ×ℝ→ℝ
  hyperbolic_smooth : ∀x,AxisC2 (hyperbolic x)
  hyperbolic_positive : ∀x,0<hyperbolic x (0,0)
  ratio_chart : ∀x,(fun w=>ratio (chart x w))=ᶠ[𝓝 (0,0)]
    (fun w=>(kind x).coefficient w/(12540153541944538512*hyperbolic x w))
  hyperbolic_curvature : ∀x,curvature (hyperbolic x)=-1

variable {X:Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem Data.actual_metric_comparison (D:Data X) :
    ∀x,(D.kind x).coefficient (0,0)≤12540153541944538512*D.hyperbolic x (0,0) :=
  SourceMetricCharts318.metric_comparison D.kind D.ratio D.ratio_continuous D.ratio_positive
    D.chart D.chart_origin D.chart_continuous D.hyperbolic D.hyperbolic_smooth
    D.hyperbolic_positive D.ratio_chart D.hyperbolic_curvature

/-- Uniform norm bounds for the exact bicanonical coefficient in every actual
chosen chart, including both branch and infinity origins. -/
theorem Data.section_norms (D:Data X) (x:X) :
    quadraticNorm (D.hyperbolic x (0,0)) (SectionCoefficientBounds318.Chart.section0 (D.kind x))≤
      4*12540153541944538512 ∧
    quadraticNorm (D.hyperbolic x (0,0)) (SectionCoefficientBounds318.Chart.section1 (D.kind x))≤
      4*12540153541944538512 :=
  comparison_norm_bound (D.kind x) (D.hyperbolic x (0,0)) 12540153541944538512
    (D.hyperbolic_positive x) (D.actual_metric_comparison x)

/-- The exact archimedean bound used by the integral-section height theorem:
actual J²-scaled coefficients, with J=2765952000. -/
theorem Data.integral_section_norms (D:Data X) (x:X) :
    quadraticNorm (D.hyperbolic x (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section0 (D.kind x))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) ∧
    quadraticNorm (D.hyperbolic x (0,0))
      ((2765952000:ℂ)^2*SectionCoefficientBounds318.Chart.section1 (D.kind x))≤
      (2765952000:ℝ)^2*(4*12540153541944538512) :=
  scaled_norm_bound (D.kind x) (D.hyperbolic x (0,0)) (D.hyperbolic_positive x)
    (D.actual_metric_comparison x)

end GlobalSectionNorm318
#print axioms GlobalSectionNorm318.Data.integral_section_norms
