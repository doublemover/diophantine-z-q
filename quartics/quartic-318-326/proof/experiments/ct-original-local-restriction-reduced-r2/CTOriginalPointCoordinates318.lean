module
public import CTOriginalFiniteWeierstrassCarrier318
public section
noncomputable section
namespace ActualTwoDescentFinitePointCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)] [DecidableEq K]

def pointCoordinates (n : K) : Point n → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

lemma actual_point_coordinates_injective (n : K) : Function.Injective (pointCoordinates n) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [pointCoordinates,WeierstrassCurve.Affine.Point.some.injEq]

end ActualTwoDescentFinitePointCardinality318
