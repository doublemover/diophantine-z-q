module
public import PELOriginalSexticRegularization318
public section
noncomputable section
namespace PELOriginalLevelTwoCubicProducts318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalSexticRatioCover318 PELOriginalPowerSectionLift318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual full degree-six section theta2_r * theta2_s squared.
It is constructed by multiplication in the original line powers. -/
@[expose] def productSection (r s : Label 2) : homogeneous τ hτ 6 :=
  multiply τ hτ 2 4 (thetaVector τ hτ 2 r)
    (multiply τ hτ 2 2 (thetaVector τ hτ 2 s) (thetaVector τ hτ 2 s))

lemma product_lift (r s : Label 2) (z : ComplexVectors) :
    lift τ hτ 6 (asSection τ hτ 6 (productSection τ hτ r s)) z =
      value τ hτ 2 r z * (value τ hτ 2 s z)^2 := by
  simp only [productSection,lift_product,theta_lift]
  ring

/-- A whole-ring matrix on every original cubic chart. Its diagonal is
exactly theta2_s cubed divided by the fixed cubic coordinate squared. -/
@[expose] def coordinate (j : Label 3) (r s : Label 2) : CoordinateChart τ hτ j :=
  PELOriginalSexticRegularization318.linear τ hτ j (productSection τ hτ r s)

lemma evaluation (j : Label 3) (r s : Label 2) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (coordinate τ hτ j r s) =
      value τ hτ 2 r z * (value τ hτ 2 s z)^2 / (value τ hτ 3 j z)^2 := by
  rw [coordinate,PELOriginalSexticRegularization318.cover_evaluation,
    coverRatio,product_lift]

@[expose] def denominator (j : Label 3) (s : Label 2) : CoordinateChart τ hτ j :=
  coordinate τ hτ j s s

lemma denominator_evaluation (j : Label 3) (s : Label 2) (z : ComplexVectors)
    (hz : value τ hτ 3 j z ≠ 0) :
    algebraEvaluation τ hτ z j hz (denominator τ hτ j s) =
      (value τ hτ 2 s z)^3 / (value τ hτ 3 j z)^2 := by
  rw [denominator,evaluation]
  ring
end PELOriginalLevelTwoCubicProducts318
