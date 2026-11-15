module
public import PELOriginalAffineChartDependence318
public import ThreeDependentTranscendenceBound318
public section
noncomputable section
namespace PELOriginalAffineChartTranscendence318
open PELOriginalCandidateAffineCharts318 PELOriginalChartSectionField318 PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
/-- The literal coordinate ring of EACH actual candidate chart has
transcendence degree at most two over its exact original complex scalars.
This follows from actual original H0 growth and ALL chart normal forms;
it is not yet a Krull-dimension equality or an analytic-image theorem. -/
theorem actual_chart_trdeg_le_two:
    Algebra.trdeg ℂ (CoordinateChart τ hτ j)≤2:=
  ThreeDependentTranscendenceBound318.trdeg_le_two
    (PELOriginalAffineChartDependence318.no_independent_triple τ hτ j)
end PELOriginalAffineChartTranscendence318
