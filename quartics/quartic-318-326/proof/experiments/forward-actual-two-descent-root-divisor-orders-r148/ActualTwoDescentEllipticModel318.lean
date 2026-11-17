module
public import ActualTwoDescentRationalBoundsProducer318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace ActualTwoDescentEllipticModel318
open WeierstrassCurve WeierstrassCurve.Affine
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]

/-- The literal original cubic, as the actual Mathlib Weierstrass model. -/
def curve (n : K) : WeierstrassCurve K := ⟨0,2*n,0,-3*n^2,0⟩
abbrev Point (n : K) := (curve n).toAffine.Point

lemma curve_equation (n x y : K) : (curve n).toAffine.Equation x y ↔ y^2=x*(x-n)*(x+3*n) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve,zero_mul,add_zero,zero_add]
  constructor <;> intro h <;> linear_combination h

lemma curve_discriminant (n : K) : (curve n).Δ=2304*n^6 := by
  simp only [WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈,curve]
  ring

lemma curve_discriminant_ne (n : K) (hn : n ≠ 0) : (curve n).Δ ≠ 0 := by
  rw [curve_discriminant]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn)

lemma curve_nonsingular (n x y : K) (hn : n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    (curve n).toAffine.Nonsingular x y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (curve_discriminant_ne n hn)).mp
    ((curve_equation n x y).mpr hc)

def point (n x y : K) (hn : n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) : Point n :=
  WeierstrassCurve.Affine.Point.some x y (curve_nonsingular n x y hn hc)

lemma point_ne_zero (n x y : K) (hn : n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    point n x y hn hc ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

lemma curve_negY (n x y : K) : (curve n).toAffine.negY x y= -y := by
  simp [WeierstrassCurve.Affine.negY,curve]

end ActualTwoDescentEllipticModel318
