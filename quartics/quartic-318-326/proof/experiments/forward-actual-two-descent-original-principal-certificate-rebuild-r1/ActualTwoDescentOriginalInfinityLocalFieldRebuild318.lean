module
public import ActualTwoDescentOriginalInfinityGenericIdentityRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityLocalFieldRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeFractionFunctions318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
variable {K : Type*} [Field K] [CharZero K]

def comparison (n : K) : (originalCubicScheme n).functionField ≃+* InfinityFractionField n :=
  IsFractionRing.ringEquivOfRingEquiv (infinityEquiv n)

lemma on_stalk (n : K) (s : InfinityStalk n) :
    comparison n (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField s)=
      infinityFractionMap n (infinityEquiv n s) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ s

lemma on_chart (n : K) (r : InfinityChart n) :
    comparison n (infinityCoefficientMap n r)=
      infinityFractionMap n (algebraMap (InfinityChart n) (InfinityLocalRing n) r) := by
  rw [←ActualTwoDescentOpenChartCoefficientRebuild318.stalk_square
    (infinityChart n) (infinityPrime n) r,on_stalk]
  exact congrArg (infinityFractionMap n)
    (ActualTwoDescentOpenAffineStalkRebuild318.coefficient_image
      (infinityChart n) (infinityPrime n) r)

lemma named_x (n : K) :
    comparison n (ActualTwoDescentOriginalGenericFunctionsRebuild318.x n)=infinityAffineX n := by
  have h := congrArg (comparison n)
    (ActualTwoDescentOriginalInfinityGenericIdentityRebuild318.x_square n)
  simp only [map_mul,on_chart] at h
  obtain ⟨e,d,he,hd,hv,hr,hunit,hy⟩ := actual_native_infinity_root_normalization n 0
  exact (eq_div_iff hv).mpr h

lemma named_coefficient (n a : K) :
    comparison n (ActualTwoDescentOriginalGenericFunctionsRebuild318.coefficient n a)=
      infinityFractionMap n (localCoefficient n a) := by
  rw [ActualTwoDescentOriginalInfinityGenericIdentityRebuild318.coefficient_affine,
    constants,on_chart] <;> rfl

/-- The previous coordinate-local pole calculation now consumes the SAME
named original scheme-generic root, through the canonical marked stalk. -/
theorem named_root (n a : K) :
    comparison n (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n a)=
      infinityAffineX n-infinityFractionMap n (localCoefficient n a) := by
  rw [ActualTwoDescentOriginalGenericFunctionsRebuild318.root_eq,map_sub,named_x,named_coefficient]
end ActualTwoDescentOriginalInfinityLocalFieldRebuild318
