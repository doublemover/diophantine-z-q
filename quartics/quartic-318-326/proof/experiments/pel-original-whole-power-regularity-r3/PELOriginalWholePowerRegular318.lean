module
public import PELOriginalWholePowerRatioGrowth318
public section
noncomputable section
namespace PELOriginalWholePowerRegular318
open QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalSectionMultiplication318
open PELOriginalWholePowerChartRatios318 PELOriginalWholePowerRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ) (j : Label 3)

/-- EVERY whole original H0(3m) section, including degree zero, has
regular ratio s/cubic_j^m on the ENTIRE algebraic chart. The caller
provides no finite model, denominator, algebraicity or growth premise. -/
theorem every_section (s : homogeneous τ hτ (3*m)) :
    ∃ a : CoordinateChart τ hτ j, ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      f a=candidateRatio τ hτ m j s (toLocus τ hτ j f) :=
  PELOriginalPolynomialGrowthRegular318.every_function τ hτ j
    (PELOriginalWholePowerRatioGrowth318.data τ hτ m j s)

/-- Exact equality at all original covering representatives, including
all former principal-open and normalization boundaries. -/
theorem every_section_on_cover (s : homogeneous τ hτ (3*m)) :
    ∃ a : CoordinateChart τ hτ j, ∀ z : ComplexVectors,
      ∀ hz : value τ hτ 3 j z ≠ 0,
      algebraEvaluation τ hτ z j hz a=coverRatio τ hτ m j s z :=
  PELOriginalPolynomialGrowthRegular318.every_function_on_cover τ hτ j
    (PELOriginalWholePowerRatioGrowth318.data τ hτ m j s)
end PELOriginalWholePowerRegular318
