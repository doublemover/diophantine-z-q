module
public import ReducedComplexPointSeparation318
public import PELOriginalRatioEvaluationExt318
public section
noncomputable section
namespace PELOriginalChartPointSeparation318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- Equality on ALL actual complex chart points is equality in the
ENTIRE original chart ring. The full ratio presentation and the original
domain theorem justify the point-separation step. -/
theorem ext (a b : CoordinateChart τ hτ j)
    (h : ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ, f a=f b) : a=b :=
  ReducedComplexPointSeparation318.ext (MvPolynomial.aeval (ratioElement τ hτ j))
    (polynomial_surjective τ hτ j) a b h
end PELOriginalChartPointSeparation318
