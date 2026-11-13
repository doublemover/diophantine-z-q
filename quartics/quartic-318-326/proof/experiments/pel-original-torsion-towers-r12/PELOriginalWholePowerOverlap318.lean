module
public import PELOriginalWholePowerSectionField318
public import PELOriginalChartOverlapLocalization318
public section
noncomputable section
namespace PELOriginalWholePowerOverlap318
open AlgebraicGeometry QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalSectionMultiplication318
open PELOriginalCandidateAffineCharts318 PELOriginalChartOverlapLocalization318
open PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ) (j k : Label 3)

/-- Exact WHOLE principal-overlap equality for every full H0(3m)
section, preserving the actual opposite-chart morphism and literal
mth power of the original cubic coordinate transition. -/
theorem transition (s : homogeneous τ hτ (3*m)) :
    algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k)
      (PELOriginalWholePowerRegularization318.linear τ hτ m j s) =
    fromOther τ hτ j k (PELOriginalWholePowerRegularization318.linear τ hτ m k s) *
      (algebraMap (CoordinateChart τ hτ j) (Overlap τ hτ j k)
        (ratioElement τ hτ j k))^m := by
  apply intoField_injective τ hτ j k
  rw [map_mul,map_pow,intoField_coefficient,intoField_coefficient,fromOther_field]
  exact PELOriginalWholePowerSectionField318.transition τ hτ m j k s
end PELOriginalWholePowerOverlap318
