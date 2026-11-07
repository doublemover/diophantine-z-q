module
public import HeightSeparation318
public section
namespace HeightSeparation318

def lucasResidual (a t z : ℝ) : ℝ := t^2-a*(a-2)*t*z+(a-2)^2*z^2-1

/-- The literal Lucas residual has the required quartic absolute-value bound. -/
theorem lucas_residual_bound (a t z B : ℝ) (hB : 3≤B)
    (ha : |a|≤B) (ht : |t|≤B) (hz : |z|≤B) :
    |lucasResidual a t z|<5*B^4 := by
  have hB0 : 0≤B := by linarith
  have ha2 : |a-2|≤B+2 := by
    have h := abs_sub a 2
    norm_num at h
    linarith
  have ht2 : t^2≤B^2 := by nlinarith [sq_abs t,abs_nonneg t]
  have hz2 : z^2≤B^2 := by nlinarith [sq_abs z,abs_nonneg z]
  have ha22 : (a-2)^2≤(B+2)^2 := by nlinarith [sq_abs (a-2),abs_nonneg (a-2)]
  have hprod : |a| * |a-2| * |t| * |z|≤B*(B+2)*B*B := by gcongr
  have hprod2 : (a-2)^2*z^2≤(B+2)^2*B^2 := by gcongr
  have htriangle : |lucasResidual a t z|≤
      t^2+|a| * |a-2| * |t| * |z|+(a-2)^2*z^2+1 := by
    unfold lucasResidual
    have h1 := abs_sub (t^2-a*(a-2)*t*z+(a-2)^2*z^2) 1
    have h2 := abs_add_le (t^2-a*(a-2)*t*z) ((a-2)^2*z^2)
    have h3 := abs_sub (t^2) (a*(a-2)*t*z)
    simp only [abs_one, abs_mul, abs_pow, sq_abs] at h1 h2 h3
    linarith
  have hpoly : B^2+B*(B+2)*B*B+(B+2)^2*B^2+1<5*B^4 := by
    have h1 : 0≤(B-3)*B^3 := by positivity
    have h2 : 0≤(B-3)*B^2 := by positivity
    have h3 : 9≤B^2 := by nlinarith
    nlinarith
  linarith

/-- With the concrete anchor, the order-13 height comparison kills the Lucas residual. -/
theorem lucas_residual_zero (a t z B c : ℝ) (hB : 3≤B)
    (ha : |a|≤B) (ht : |t|≤B) (hz : |z|≤B)
    (hanchor : (2:ℝ)^49151<c) (hcB : c≤B+1)
    (hheight : lucasResidual a t z≠0 → B^2-6<7*heightConstant*
      |lucasResidual a t z|^((49:ℝ)/104)) :
    lucasResidual a t z=0 := by
  by_contra hd
  exact high_defect_contradiction heightConstant B |lucasResidual a t z| c
    heightConstant_ge_one hB (abs_nonneg _) (lucas_residual_bound a t z B hB ha ht hz)
    (hheight hd) (anchor_high_margin c hanchor) hcB

end HeightSeparation318
