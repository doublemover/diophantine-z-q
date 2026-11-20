module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace ActualTwoDescentFiniteEllipticModel318
open WeierstrassCurve WeierstrassCurve.Affine
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]

/-- The literal original cubic, as the actual Mathlib Weierstrass model. -/
@[expose] def curve (n : K) : WeierstrassCurve K := ⟨0,2*n,0,-3*n^2,0⟩
abbrev Point (n : K) := (curve n).toAffine.Point

end ActualTwoDescentFiniteEllipticModel318
