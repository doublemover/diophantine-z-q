module
public import ActualTwoDescentOpenChartGenericFieldRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalGenericFunctionsRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentAffineChartCoordinates318
variable {K : Type*} [Field K] [CharZero K]

abbrev GenericField (n : K) := (originalCubicScheme n).functionField
def affineComparison (n : K) : GenericField n ≃+* OriginalFunctionField n :=
  ActualTwoDescentOpenChartGenericFieldRebuild318.fractionComparison (affineChart n)
def coefficient (n : K) : K →+* GenericField n :=
  (affineComparison n).symm.toRingHom.comp (functionCoefficientMap n)
def x (n : K) : GenericField n := (affineComparison n).symm (functionX n)
def root (n a : K) : GenericField n := (affineComparison n).symm (rootFunction n a)

lemma root_eq (n a : K) : root n a = x n - coefficient n a := by
  unfold root x coefficient
  rw [actual_root_function_identity, map_sub] <;> rfl
lemma root_nonzero (n a : K) : root n a ≠ 0 := by
  intro h
  apply actual_root_function_nonzero n a
  have hh := congrArg (affineComparison n) h
  simpa only [root,RingEquiv.apply_symm_apply,map_zero] using hh
lemma root_comparison (n a : K) :
    affineComparison n (root n a) = rootFunction n a :=
  (affineComparison n).apply_symm_apply _

/-- All source elements are recovered through the same actual generic
stalk comparison. Local specialization squares remain a separate join. -/
lemma exact_inverse (n : K) (f : GenericField n) :
    (affineComparison n).symm (affineComparison n f) = f :=
  (affineComparison n).symm_apply_apply f
end ActualTwoDescentOriginalGenericFunctionsRebuild318
