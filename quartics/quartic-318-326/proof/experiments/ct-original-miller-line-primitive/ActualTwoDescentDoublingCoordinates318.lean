module
public import ActualTwoDescentEllipticModel318
import all ActualTwoDescentEllipticModel318
public section
noncomputable section
namespace ActualTwoDescentDoublingCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318
variable [DecidableEq K]

def tangent (n x y : K) := (3*x^2+4*n*x-3*n^2)/(2*y)
def doubleX (n x y : K) := (tangent n x y)^2-2*n-2*x

lemma actual_tangent (n x y : K) (hy : y ≠ 0) :
    (curve n).toAffine.slope x x y y=tangent n x y := by
  have hy' : y ≠ (curve n).toAffine.negY x y := by
    rw [curve_negY]
    intro he
    apply hy
    linear_combination he/2
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy',curve_negY]
  dsimp [curve,tangent]
  congr 1 <;> ring

lemma actual_addX_double (n x y : K) (hy : y ≠ 0) :
    (curve n).toAffine.addX x x ((curve n).toAffine.slope x x y y)=doubleX n x y := by
  rw [actual_tangent n x y hy]
  dsimp [WeierstrassCurve.Affine.addX,curve,doubleX]
  ring

end ActualTwoDescentDoublingCoordinates318
