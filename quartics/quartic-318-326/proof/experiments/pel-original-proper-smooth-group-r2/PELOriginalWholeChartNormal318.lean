module
public import NormalFromPointwisePrincipalOpens318
public import PELOriginalNormalSmoothNeighborhood318
public section
noncomputable section
namespace PELOriginalWholeChartNormal318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- The WHOLE original coordinate chart is integrally closed, with its
actual scalar structure and fraction field. All charts and all old
denominator boundaries are covered by genuine normal principal opens. -/
theorem integrallyClosed : IsIntegrallyClosed (CoordinateChart τ hτ j) := by
  apply NormalFromPointwisePrincipalOpens318.integrallyClosed
  · intro I hI
    exact ProperIdealComplexPoint318.exists_point (MvPolynomial.aeval (ratioElement τ hτ j))
      (polynomial_surjective τ hτ j) I hI
  · intro f
    obtain ⟨x,hx,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
    obtain ⟨d,hd,hn,ho,hs,u,hu⟩ := PELOriginalNormalSmoothNeighborhood318.original_point τ hτ j x hx
    refine ⟨d,?_,hn⟩
    rw [hf]
    exact hd

/-- Every element of the ACTUAL fraction field integral over the whole
chart is already an element of that SAME chart ring. This is the direct
regular-section consumer, with no abstract normal model substituted. -/
theorem integral_fraction_is_regular (y : FractionRing (CoordinateChart τ hτ j))
    (hy : IsIntegral (CoordinateChart τ hτ j) y) :
    ∃ a : CoordinateChart τ hτ j,
      algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j)) a = y := by
  letI := integrallyClosed τ hτ j
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hy
end PELOriginalWholeChartNormal318
