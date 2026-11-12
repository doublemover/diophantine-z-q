module
public import ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityGenericIdentityRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
open ActualTwoDescentOriginalGenericFunctionsRebuild318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

lemma x_affine (n : K) : x n=affineCoefficientMap n (affineX n) := by
  apply (affineComparison n).injective
  rw [show affineComparison n (x n)=
    ActualTwoDescentOriginalFunctionFieldTheta318.functionX n from
      (affineComparison n).apply_symm_apply _]
  exact (ActualTwoDescentOpenChartCoefficientRebuild318.fraction_comparison
    (affineChart n) (affineX n)).symm

lemma coefficient_affine (n a : K) :
    coefficient n a=affineCoefficientMap n (affineCoefficient n a) := by
  apply (affineComparison n).injective
  change affineComparison n ((affineComparison n).symm
    (ActualTwoDescentOriginalFunctionFieldTheta318.functionCoefficientMap n a))=_
  rw [RingEquiv.apply_symm_apply]
  exact (ActualTwoDescentOpenChartCoefficientRebuild318.fraction_comparison
    (affineChart n) (affineCoefficient n a)).symm

lemma v_nonzero (n : K) : infinityCoefficientMap n (chartV n) ≠ 0 := by
  intro h
  apply ActualTwoDescentInfinityNativeDomain318.actual_chart_v_nonzero n
  apply ActualTwoDescentOpenChartCoefficientRebuild318.injective (infinityChart n)
  simpa only [map_zero] using h

lemma x_square (n : K) :
    x n*infinityCoefficientMap n (chartV n)=infinityCoefficientMap n (chartU n) := by
  rw [x_affine]
  exact x_times_v n

/-- Same named ORIGINAL root function, exact native infinity coordinate map. -/
theorem root_square (n a : K) :
    root n a*infinityCoefficientMap n (chartV n)=
      infinityCoefficientMap n (chartU n-chartCoefficient n a*chartV n) := by
  rw [root_eq,sub_mul,x_square,coefficient_affine,constants,map_sub,map_mul]

theorem root_quotient (n a : K) :
    root n a=infinityCoefficientMap n (chartU n-chartCoefficient n a*chartV n)/
      infinityCoefficientMap n (chartV n) :=
  (eq_div_iff (v_nonzero n)).mpr (root_square n a)
end ActualTwoDescentOriginalInfinityGenericIdentityRebuild318
