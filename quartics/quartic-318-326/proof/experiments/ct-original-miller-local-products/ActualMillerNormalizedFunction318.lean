module
public import ActualTwoDescentAffineChartCoordinates318
public import ActualTwoDescentOriginalFunctionFieldTheta318
public section
noncomputable section
namespace ActualMillerInfinityNormalization318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalFunctionFieldTheta318
variable {K : Type*} [Field K] [CharZero K]

/-- The signed tangent/secant divided by the vertical line, in the
actual original function field. The slope and sum coordinate are
supplied by the native affine point formulas at the call site. -/
def nonverticalFunction (n x y a z : K) : OriginalFunctionField n :=
  (functionCoefficientMap n a * (functionX n - functionCoefficientMap n x) +
    functionCoefficientMap n y - algebraMap (AffineChart n) _ (affineY n)) /
    (functionX n - functionCoefficientMap n z)

end ActualMillerInfinityNormalization318
