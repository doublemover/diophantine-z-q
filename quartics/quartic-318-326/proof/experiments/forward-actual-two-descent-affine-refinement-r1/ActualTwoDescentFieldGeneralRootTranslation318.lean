module
public import ActualTwoDescentFieldSquarePairGaloisEquivalence318
public section
noncomputable section
namespace ActualTwoDescentFieldGeneralRootTranslation318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def rootDerivative (n e : K) : K := 3*e^2+4*n*e-3*n^2

lemma actual_root_secant (n x y e : K) (hx : x-e ≠ 0) :
    (curve n).toAffine.slope x e y 0=y/(x-e) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (sub_ne_zero.mp hx)]
  congr 1 <;> ring

lemma actual_root_addX (n x y e : K) (hx : x-e ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (he : e*(e-n)*(e+3*n)=0) :
    (curve n).toAffine.addX x e ((curve n).toAffine.slope x e y 0)=e+rootDerivative n e/(x-e) := by
  rw [actual_root_secant n x y e hx]
  dsimp [WeierstrassCurve.Affine.addX,curve,rootDerivative]
  field_simp [hx]
  <;> linear_combination hc-he

lemma actual_root_addY (n x y e : K) (hx : x-e ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (he : e*(e-n)*(e+3*n)=0) :
    (curve n).toAffine.addY x e y ((curve n).toAffine.slope x e y 0)= -rootDerivative n e*y/(x-e)^2 := by
  rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY,
    actual_root_addX n x y e hx hc he,actual_root_secant n x y e hx]
  field_simp [hx]
  <;> ring

/-- Generic addition by an ACTUAL rational two-torsion root, with original curve/group law. -/
theorem actual_add_root_point (n x y e X Y : K) (hn : n ≠ 0) (hx : x-e ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (he : e*(e-n)*(e+3*n)=0)
    (hC : Y^2=X*(X-n)*(X+3*n))
    (hX : X=e+rootDerivative n e/(x-e)) (hY : Y= -rootDerivative n e*y/(x-e)^2) :
    point n x y hn hc+point n e 0 hn (by simpa using he.symm)=point n X Y hn hC := by
  unfold point
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (sub_ne_zero.mp hx)]
  congr 1
  · exact (actual_root_addX n x y e hx hc he).trans hX.symm
  · exact (actual_root_addY n x y e hx hc he).trans hY.symm

end ActualTwoDescentFieldGeneralRootTranslation318
