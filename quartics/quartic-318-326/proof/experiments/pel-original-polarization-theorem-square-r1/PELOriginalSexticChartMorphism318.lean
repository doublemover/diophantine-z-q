module
public import AffineComplexProjectiveVector318
public import PELOriginalSexticBasepointFree318
public section
noncomputable section
namespace PELOriginalSexticChartMorphism318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open ComplexProjectiveMarkerPoint318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalSexticRegularization318
variable (τ : ℂ) (hτ : 0<τ.im) (j : Label 3)
local instance standardGrading : GradedAlgebra (grading (ι := Label 6)) := MvPolynomial.gradedAlgebra

/-- The actual whole original cubic chart maps REGULARLY to level-six
projective space. This uses the actual regularized sextic sections and
unit ideal, not a projective normal-generation hypothesis. -/
@[expose] def morphism : Spec (CommRingCat.of (CoordinateChart τ hτ j)) ⟶
    Proj (grading (ι := Label 6)) :=
  AffineComplexProjectiveVector318.morphism (theta τ hτ j)
    (PELOriginalSexticBasepointFree318.span_eq_top τ hτ j)

@[reassoc] theorem over_complex :
    morphism τ hτ j≫ComplexProjectiveBase318.structureMap=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ j))) :=
  AffineComplexProjectiveVector318.over_complex _ _

lemma ratio_nonzero (z : ComplexVectors) (hz : value τ hτ 3 j z≠0) :
    ∃ r : Label 6, value τ hτ 6 r z/(value τ hτ 3 j z)^2≠0 := by
  have h := AffineComplexProjectiveVector318.evaluation_nonzero (theta τ hτ j)
    (PELOriginalSexticBasepointFree318.span_eq_top τ hτ j)
    (algebraEvaluation τ hτ z j hz)
  simpa only [theta_evaluation] using h

/-- Exact original sextic-ratio action at all original chart lifts,
including the former primitive-open boundary. -/
theorem original_point_action (z : ComplexVectors) (hz : value τ hτ 3 j z≠0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫morphism τ hτ j=
      ComplexProjectiveSchemePoint318.point
        (fun r : Label 6 => value τ hτ 6 r z/(value τ hτ 3 j z)^2)
        (ratio_nonzero τ hτ j z hz) := by
  have h := AffineComplexProjectiveVector318.point_action (theta τ hτ j)
    (PELOriginalSexticBasepointFree318.span_eq_top τ hτ j)
    (algebraEvaluation τ hτ z j hz)
  simpa only [theta_evaluation] using h
end PELOriginalSexticChartMorphism318
