module
public import ActualTwoDescentSquareClassFieldMap318
public section
noncomputable section
namespace ActualTwoDescentEllipticFieldCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318
variable {L : Type*} [Field L] [CharZero L] [DecidableEq K] [DecidableEq L]

lemma actual_curve_equation_map (f : K →+* L) (n x y : K) (h : y^2=x*(x-n)*(x+3*n)) :
    (f y)^2=f x*(f x-f n)*(f x+3*f n) := by
  simpa only [map_pow,map_mul,map_sub,map_add,map_ofNat] using congrArg f h

lemma actual_curve_map (f : K →+* L) (n : K) : (curve n).toAffine.map f=(curve (f n)).toAffine := by
  ext <;> simp [curve,WeierstrassCurve.map]

lemma actual_negY_map (f : K →+* L) (n x y : K) :
    (curve (f n)).toAffine.negY (f x) (f y)=f ((curve n).toAffine.negY x y) := by
  rw [←actual_curve_map f n]
  exact WeierstrassCurve.Affine.map_negY f x y

lemma actual_slope_map (f : K →+* L) (n x₁ x₂ y₁ y₂ : K) :
    (curve (f n)).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂)=
      f ((curve n).toAffine.slope x₁ x₂ y₁ y₂) := by
  rw [←actual_curve_map f n]
  exact WeierstrassCurve.Affine.map_slope f x₁ x₂ y₁ y₂

lemma actual_addX_map (f : K →+* L) (n x₁ x₂ m : K) :
    (curve (f n)).toAffine.addX (f x₁) (f x₂) (f m)=f ((curve n).toAffine.addX x₁ x₂ m) := by
  rw [←actual_curve_map f n]
  exact WeierstrassCurve.Affine.map_addX f x₁ x₂ m

lemma actual_addY_map (f : K →+* L) (n x₁ x₂ y m : K) :
    (curve (f n)).toAffine.addY (f x₁) (f x₂) (f y) (f m)=f ((curve n).toAffine.addY x₁ x₂ y m) := by
  rw [←actual_curve_map f n]
  exact WeierstrassCurve.Affine.map_addY f x₁ x₂ y m

end ActualTwoDescentEllipticFieldCoordinates318
