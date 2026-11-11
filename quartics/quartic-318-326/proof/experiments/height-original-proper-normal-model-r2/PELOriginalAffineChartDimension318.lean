module
public import PELOriginalAffineChartTranscendence318
public import PELOriginalCandidateChartFiniteType318
public import FiniteTypeSurfaceDimension318
public section
noncomputable section
namespace PELOriginalAffineChartDimension318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateChartDomains318
open PELOriginalChartSectionField318 PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)(j:Label 3)
local instance actualDomain:IsDomain (CoordinateChart τ hτ j):=coordinate_chart_domain τ hτ j
local instance actualFiniteType:Algebra.FiniteType ℂ (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
/-- Every literal candidate chart admits a genuine integral Noether
normalization with at most TWO polynomial coordinates over its ORIGINAL
complex scalar action. No formal replacement of the chart ring occurs. -/
theorem actual_normalization_two:
    ∃s:ℕ,s≤2∧∃g:MvPolynomial (Fin s) ℂ→ₐ[ℂ]CoordinateChart τ hτ j,
      Function.Injective g∧g.IsIntegral:=
  FiniteTypeSurfaceDimension318.normalization_two (CoordinateChart τ hτ j)
    (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
/-- The ACTUAL coordinate ring of each of the nine genuine candidate
charts has Krull dimension at most two. Analytic-image equality,
projective normality, and a lower dimension bound remain separate. -/
theorem actual_chart_dimension_le_two:ringKrullDim (CoordinateChart τ hτ j)≤2:=
  FiniteTypeSurfaceDimension318.krull_dimension_le_two (CoordinateChart τ hτ j)
    (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
end PELOriginalAffineChartDimension318
