module
public import ActualTwoDescentFourObstructionConsumer318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace ActualTwoDescentFiniteEllipticModel318
open WeierstrassCurve WeierstrassCurve.Affine
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]

lemma good_two_ne : (2 : K) ≠ 0 := NeZero.ne _
lemma good_three_ne : (3 : K) ≠ 0 := NeZero.ne _
lemma good_four_ne : (4 : K) ≠ 0 := by
  rw [show (4 : K)=2*2 by ring]
  exact mul_ne_zero good_two_ne good_two_ne
lemma good_twelve_ne : (12 : K) ≠ 0 := by
  rw [show (12 : K)=3*4 by ring]
  exact mul_ne_zero good_three_ne good_four_ne
lemma good_sixteen_ne : (16 : K) ≠ 0 := by
  rw [show (16 : K)=4*4 by ring]
  exact mul_ne_zero good_four_ne good_four_ne
lemma good_discriminant_ne : (2304 : K) ≠ 0 := by
  rw [show (2304 : K)=2^8*3^2 by ring]
  exact mul_ne_zero (pow_ne_zero _ good_two_ne) (pow_ne_zero _ good_three_ne)
lemma good_ne_neg {a : K} (ha : a ≠ 0) : a ≠ -a := by
  intro h
  apply mul_ne_zero good_two_ne ha
  linear_combination h

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
  exact mul_ne_zero good_discriminant_ne (pow_ne_zero _ hn)

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

end ActualTwoDescentFiniteEllipticModel318
