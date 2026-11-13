module
public import ActualTwoDescentFiniteHalvingCoordinates318
public section
noncomputable section
namespace ActualTwoDescentFiniteHalvingGroup318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]


open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentFiniteHalvingCoordinates318
variable [DecidableEq K]

lemma actual_half_slope (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    (curve n).toAffine.slope (halfX x a b c) (halfX x a b c)
      (halfY a b c) (halfY a b c)=halfSlope a b c := by
  have hY := half_y_nonzero n x a b c hn ha hb hc
  have hy : halfY a b c ≠ (curve n).toAffine.negY (halfX x a b c) (halfY a b c) := by
    rw [curve_negY]
    exact good_ne_neg hY
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,curve_negY]
  simp only [curve,zero_mul,sub_zero]
  apply (div_eq_iff (mul_ne_zero good_two_ne hY)).mpr
  linear_combination -(half_tangent n x a b c ha hb hc)

/-- The explicit root formula halves the ORIGINAL point in the actual elliptic group. -/
theorem actual_half_add_self (n x y a b c : K) (hn : n ≠ 0)
    (hxy : y^2=x*(x-n)*(x+3*n))
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) (hprod : a*b*c= -y) :
    point n (halfX x a b c) (halfY a b c) hn (half_curve n x a b c ha hb hc) +
    point n (halfX x a b c) (halfY a b c) hn (half_curve n x a b c ha hb hc) =
    point n x y hn hxy := by
  have hY := half_y_nonzero n x a b c hn ha hb hc
  have hy : halfY a b c ≠ (curve n).toAffine.negY (halfX x a b c) (halfY a b c) := by
    rw [curve_negY]
    exact good_ne_neg hY
  have hs := actual_half_slope n x a b c hn ha hb hc
  have hX : (curve n).toAffine.addX (halfX x a b c) (halfX x a b c) (halfSlope a b c)=x := by
    simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero]
    linear_combination half_double_x n x a b c ha hb hc
  have hYY : (curve n).toAffine.addY (halfX x a b c) (halfX x a b c)
      (halfY a b c) (halfSlope a b c)=y := by
    rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY,hX]
    linear_combination half_double_y x y a b c hprod
  unfold point
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  congr 1
  · rw [hs,hX]
  · rw [hs,hYY]

end ActualTwoDescentFiniteHalvingGroup318
