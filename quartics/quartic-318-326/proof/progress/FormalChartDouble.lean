module
public import FormalChartNorm
public import ReciprocalDouble318
public section
noncomputable section
namespace FormalChartDouble
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
variable {F:Type*} [Field F] [CharZero F] [DecidableEq F]

lemma ordinate_equation (D x y:F) (h:(E D).Nonsingular x y) : y^2=x^3-D*x := by
  simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1

lemma affine_double_square (D x y:F) (h:(E D).Nonsingular x y) (hy:y≠0) :
    (E D).addX x x ((E D).slope x x y y)=((x^2+D)/(2*y))^2 := by
  have hneg : y≠(E D).negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    have hz : 2*y=0 := by linear_combination hh
    exact (mul_ne_zero (by norm_num) hy) hz
  have hc := ordinate_equation D x y h
  have hs : (E D).slope x x y y=(3*x^2-D)/(2*y) := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
    congr 1 <;> ring
  rw [addX,hs]
  simp only [E,zero_mul,add_zero,sub_zero]
  field_simp [hy]
  linear_combination -8*x*hc

lemma double_square_pole (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D x y:F) (hD:w D≤1) (hx:1<w x) (hc:y^2=x^3-D*x) :
    1<w (((x^2+D)/(2*y))^2) := by
  have hxp : 0<w x := lt_trans (by norm_num) hx
  have hlt : w (-(D*x))<w (x^3) := by
    rw [map_neg_eq_map,map_mul,map_pow]
    have hxx : w x<w x^3 := by nlinarith [sq_nonneg (w x-1)]
    exact (mul_le_of_le_one_left (apply_nonneg w x) hD).trans_lt hxx
  have hyc : w y^2=w x^3 := by
    have hh := congrArg w hc
    rw [map_pow,sub_eq_add_neg,hna.add_eq_left_of_lt (map_neg_eq_map w) hlt,map_pow] at hh
    exact hh
  have hnum : w (x^2+D)=w x^2 := by
    have hh : w D<w (x^2) := by rw [map_pow]; nlinarith
    rw [hna.add_eq_left_of_lt (map_neg_eq_map w) hh,map_pow]
  have h2 : w (2:F)≤1 := hna.apply_natCast_le_one (map_zero_le w 1) (map_one w)
  have h2p : 0<w (2:F) := w.pos (by norm_num)
  have h2sq : w (2:F)^2≤1 := by nlinarith [apply_nonneg w (2:F)]
  rw [map_pow,map_div₀,hnum,map_mul,div_pow,mul_pow,hyc]
  apply (one_lt_div (mul_pos (sq_pos_of_pos h2p) (pow_pos hxp 3))).mpr
  have hden : w (2:F)^2*w x^3≤w x^3 :=
    mul_le_of_le_one_left (pow_nonneg (apply_nonneg w x) 3) h2sq
  have hg : w x^3<(w x^2)^2 := by nlinarith [pow_pos hxp 3]
  exact hden.trans_lt hg

/-- Actual Mathlib doubling of every affine x-pole stays an x-pole.
The stronger conclusion excludes infinity rather than requiring a disjunction. -/
theorem actual_double_pole (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D x y:F) (h:(E D).Nonsingular x y) (hD:w D≤1) (hx:1<w x) :
    1<w (((Point.some x y h)+(Point.some x y h)).xRep 0) := by
  have hc := ordinate_equation D x y h
  have hy := (FormalChartNorm.affine_to_small_chart w hna D x y hD hx hc).1
  have hneg : y≠(E D).negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    have hz : 2*y=0 := by linear_combination hh
    exact (mul_ne_zero (by norm_num) hy) hz
  rw [Point.add_self_of_Y_ne hneg]
  simp only [Point.xRep_some,Matrix.cons_val_zero]
  rw [affine_double_square D x y h hy]
  exact double_square_pole w hna D x y hD hx hc

/-- Point-level version ready for subgroup closure, including the identity branch. -/
theorem point_double_pole (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D:F) (Q:(E D).Point) (hD:w D≤1) (hx:1<w (Q.xRep 0)) :
    1<w ((Q+Q).xRep 0) := by
  cases Q with
  | zero =>
    change 1<w (((0:(E D).Point)).xRep 0) at hx
    simp only [Point.xRep_zero,Matrix.cons_val_zero,map_one] at hx
    exact False.elim (lt_irrefl (1:ℝ) hx)
  | some x y h =>
    simp only [Point.xRep_some,Matrix.cons_val_zero] at hx
    exact actual_double_pole w hna D x y h hD hx

#print axioms ordinate_equation
#print axioms affine_double_square
#print axioms double_square_pole
#print axioms actual_double_pole
#print axioms point_double_pole
end FormalChartDouble
