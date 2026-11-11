module
public import PELOriginalLevelTwoRegularMatrix318
public import PELOriginalLevelTwoSchemePoint318
public import RankOneAffinePointAction318
public section
noncomputable section
namespace PELOriginalLevelTwoChartMorphism318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidateNineChartCover318
open PELOriginalLevelTwoCubicProducts318 PELOriginalLevelTwoRegularMatrix318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
local instance chartFinite : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) :=
  chart_finite_type τ hτ j
local instance standardGrading : GradedAlgebra
    (ComplexProjectiveMarkerPoint318.grading (ι := Label 2)) := MvPolynomial.gradedAlgebra

/-- Genuine regular map from the WHOLE original cubic chart to P³.
The existing all-entry principal cover and rank-one column glue apply
to the literal degree-six products, without quadratic normal generation. -/
@[expose] def morphism : Spec (CommRingCat.of (CoordinateChart τ hτ j)) ⟶
    Proj (ComplexProjectiveMarkerPoint318.grading (ι := Label 2)) :=
  RankOneAffineProjectiveMorphism318.morphism (coordinate τ hτ j)
    (entry_span τ hτ j) (minors τ hτ j)

@[reassoc] theorem over_complex :
    morphism τ hτ j ≫ ComplexProjectiveBase318.structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j))) :=
  RankOneAffineProjectiveMorphism318.over_complex _ _ _

/-- Exact original level-two point action on every chart point. All
input theta characteristics, powers and original cubic denominator are
kept until the actual Segre column is evaluated. -/
theorem chart_action (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom) ≫
      morphism τ hτ j = PELOriginalLevelTwoSchemePoint318.point τ hτ (projection (P τ) z) := by
  have he := RankOneAffinePointAction318.segre_action
    (coordinate τ hτ j) (entry_span τ hτ j) (minors τ hτ j)
    (algebraEvaluation τ hτ z j hz)
    (fun r : Label 2 => value τ hτ 2 r z)
    (fun s : Label 2 => (value τ hτ 2 s z)^2 / (value τ hτ 3 j z)^2)
    (PELOriginalLevelTwoSchemePoint318.cover_nonzero τ hτ z)
    (by intro r s; rw [evaluation]; exact mul_div_assoc _ _ _)
  exact he.trans (PELOriginalLevelTwoSchemePoint318.covering_point τ hτ z)
end PELOriginalLevelTwoChartMorphism318
