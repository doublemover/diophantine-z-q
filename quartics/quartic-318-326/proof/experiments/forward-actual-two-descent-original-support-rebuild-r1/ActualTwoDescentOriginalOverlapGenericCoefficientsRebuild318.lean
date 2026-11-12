module
public import ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318
public import ActualTwoDescentOriginalRootLocalFieldRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

def commonChart (n : K) : overlapScheme n ⟶ originalCubicScheme n :=
  intoInfinity n ≫ infinityChart n
instance commonChart_open (n : K) : IsOpenImmersion (commonChart n) := by
  unfold commonChart
  infer_instance

def affineCoefficientMap (n : K) : AffineChart n →+* (originalCubicScheme n).functionField :=
  ActualTwoDescentOpenChartCoefficientRebuild318.coefficient (affineChart n)
def infinityCoefficientMap (n : K) : InfinityChart n →+* (originalCubicScheme n).functionField :=
  ActualTwoDescentOpenChartCoefficientRebuild318.coefficient (infinityChart n)
def overlapCoefficientMap (n : K) : InfinityPuncture n →+* (originalCubicScheme n).functionField :=
  ActualTwoDescentOpenChartCoefficientRebuild318.coefficient (commonChart n)

lemma infinity_square (n : K) (r : InfinityChart n) :
    infinityCoefficientMap n r=overlapCoefficientMap n (infinityOpenMap n r) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityOpenMap n))) :=
    intoInfinity_open n
  exact ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318.coefficient
    (infinityChart n) (commonChart n) (infinityOpenMap n) rfl r

lemma affine_square (n : K) (r : AffineChart n) :
    affineCoefficientMap n r=overlapCoefficientMap n (affineToInfinity n r) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineToInfinity n))) := by
    rw [←actual_into_affine]
    infer_instance
  apply ActualTwoDescentOpenChartCoefficientCompatibilityRebuild318.coefficient
    (affineChart n) (commonChart n) (affineToInfinity n)
  rw [←actual_into_affine]
  exact pushout.condition

/-- Agreement of the original constant coefficients, not a chosen field isomorphism. -/
lemma constants (n a : K) :
    affineCoefficientMap n (affineCoefficient n a)=
      infinityCoefficientMap n (chartCoefficient n a) := by
  rw [affine_square,infinity_square,actual_affine_to_infinity_coefficient] <;> rfl

lemma x_times_v (n : K) :
    affineCoefficientMap n (affineX n)*infinityCoefficientMap n (chartV n)=
      infinityCoefficientMap n (chartU n) := by
  rw [affine_square,infinity_square,infinity_square,actual_affine_to_infinity_x,←map_mul]
  apply congrArg (overlapCoefficientMap n)
  change (openU n*inverseV n)*openV n=openU n
  calc
    _=openU n*(openV n*inverseV n) := by ring
    _=openU n := by rw [actual_open_v_inverse,mul_one]
end ActualTwoDescentOriginalOverlapGenericCoefficientsRebuild318
