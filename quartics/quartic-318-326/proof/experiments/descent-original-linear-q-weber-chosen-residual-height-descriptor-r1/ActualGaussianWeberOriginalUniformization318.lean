module
public import ActualGaussianComplexTorusCore318
public import ActualGaussianWeberQuarterTurn318
public import ActualGaussianWeberSelectedGaussianPrime318
public section
noncomputable section

namespace ActualGaussianWeberComplexUniformizationFibres318
open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberSelectedGaussianPrime318

attribute [local instance] Classical.decEq

/-- The one classical analytic input: the literal square complex
torus uniformizes the original curve and the positive i action
is the original coordinate quarter-turn. No fibres or degrees are
part of this condition. -/
structure OriginalUniformization where
  point : Torus ≃+ WP ℂ
  quarter : ∀ P : Torus, point (scalar gaussianI P) =
    turn (by norm_num : (2:ℂ)≠0) Complex.I Complex.I_sq (point P)

end ActualGaussianWeberComplexUniformizationFibres318
