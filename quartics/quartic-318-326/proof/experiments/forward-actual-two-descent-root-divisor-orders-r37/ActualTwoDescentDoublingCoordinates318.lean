module
public import ActualTwoDescentIdentityClassHalving318
public section
noncomputable section
namespace ActualTwoDescentDoublingCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentTorsionSquarePairs318
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

lemma actual_double_squares (n x y : K) (hy : y ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    doubleX n x y=((x^2+3*n^2)/(2*y))^2 ∧
    doubleX n x y-n=(((x-n)^2-4*n^2)/(2*y))^2 ∧
    doubleX n x y+3*n=(((x+3*n)^2-12*n^2)/(2*y))^2 := by
  constructor
  · calc
      doubleX n x y=((3*x^2+4*n*x-3*n^2)^2+4*y^2*(-2*n-2*x))/(2*y)^2 := by
        dsimp [doubleX,tangent]
        field_simp [hy]
        <;> ring
      _=(x^2+3*n^2)^2/(2*y)^2 := by
        congr 1
        linear_combination (-8*n-8*x)*hc
      _=((x^2+3*n^2)/(2*y))^2 := by rw [div_pow]
  constructor
  · calc
      doubleX n x y-n=((3*x^2+4*n*x-3*n^2)^2+4*y^2*(-2*n-2*x-n))/(2*y)^2 := by
        dsimp [doubleX,tangent]
        field_simp [hy]
        <;> ring
      _=((x-n)^2-4*n^2)^2/(2*y)^2 := by
        congr 1
        linear_combination (-12*n-8*x)*hc
      _=(((x-n)^2-4*n^2)/(2*y))^2 := by rw [div_pow]
  · calc
      doubleX n x y+3*n=((3*x^2+4*n*x-3*n^2)^2+4*y^2*(-2*n-2*x+3*n))/(2*y)^2 := by
        dsimp [doubleX,tangent]
        field_simp [hy]
        <;> ring
      _=((x+3*n)^2-12*n^2)^2/(2*y)^2 := by
        congr 1
        linear_combination (4*n-8*x)*hc
      _=(((x+3*n)^2-12*n^2)/(2*y))^2 := by rw [div_pow]

/-- Every non-two-torsion double has the literal identity Kummer class. -/
theorem actual_double_identity_class (n x y : K) (hy : y ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n))
    (hB : doubleX n x y-n ≠ 0) (hA : doubleX n x y+3*n ≠ 0) :
    SquarePair (doubleX n x y+3*n) (doubleX n x y-n) 1 1 := by
  obtain ⟨hx,hb,ha⟩ := actual_double_squares n x y hy hc
  refine ⟨((x+3*n)^2-12*n^2)/(2*y),((x-n)^2-4*n^2)/(2*y),?_,?_,?_,?_⟩
  · intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at ha
    exact hA ha
  · intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hb
    exact hB hb
  · simpa only [one_mul] using ha
  · simpa only [one_mul] using hb

end ActualTwoDescentDoublingCoordinates318
