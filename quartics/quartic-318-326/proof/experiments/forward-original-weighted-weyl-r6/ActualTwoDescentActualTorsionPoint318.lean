module
public import ActualTwoDescentIdentityClassKernel318
public section
noncomputable section
namespace ActualTwoDescentActualTorsionPoint318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318
variable [DecidableEq K]

lemma torsion_curve (n : K) : (0 : K)^2=(-3*n)*(-3*n-n)*(-3*n+3*n) := by ring

def torsionPoint (n : K) (hn : n ≠ 0) : Point n := point n (-3*n) 0 hn (torsion_curve n)

lemma actual_torsion_nonzero (n : K) (hn : n ≠ 0) : torsionPoint n hn ≠ 0 := point_ne_zero _ _ _ _ _

lemma actual_torsion_double_zero (n : K) (hn : n ≠ 0) : torsionPoint n hn+torsionPoint n hn=0 := by
  unfold torsionPoint point
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [curve_negY]
  ring

end ActualTwoDescentActualTorsionPoint318
