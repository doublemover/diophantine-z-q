module
public import Mathlib.NumberTheory.Height.NumberField
public section
namespace FormalChartNorm
set_option maxHeartbeats 0
variable {F:Type*} [Field F] (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)

include hna in
lemma small_add {a b:F} (ha:w a<1) (hb:w b<1) : w (a+b)<1 :=
  (hna a b).trans_lt (max_lt ha hb)
include hna in
lemma small_sub {a b:F} (ha:w a<1) (hb:w b<1) : w (a-b)<1 := by
  simpa only [sub_eq_add_neg] using small_add w hna ha (by simpa only [map_neg_eq_map] using hb)
lemma small_mul {a b:F} (ha:w a≤1) (hb:w b<1) : w (a*b)<1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left (apply_nonneg w b) ha).trans_lt hb
lemma small_square {a:F} (ha:w a<1) : w (a^2)<1 := by
  simpa only [pow_two] using small_mul w ha.le ha
include hna in
lemma one_add_unit {a:F} (ha:w a<1) : w (1+a)=1 := by
  simpa only [map_one] using hna.add_eq_left_of_lt (map_neg_eq_map w)
    (show w a<w (1:F) by simpa using ha)
include hna in
lemma one_sub_unit {a:F} (ha:w a<1) : w (1-a)=1 := by
  simpa only [sub_eq_add_neg] using one_add_unit w hna (by simpa only [map_neg_eq_map] using ha)

include hna in
/-- Actual affine curve equation and a pole of x produce the small formal
chart z=-x/y, t=-1/y; no formal series or Hensel premise is used. -/
lemma affine_to_small_chart (D x y:F) (hD:w D≤1) (hx:1<w x)
    (hc:y^2=x^3-D*x) :
    y≠0 ∧ 1<w y ∧ w (-x/y)<1 ∧ w (-1/y)<1 ∧
      (-1/y)=(-x/y)^3-D*(-x/y)*(-1/y)^2 := by
  have hxp : 0<w x := lt_trans (by norm_num) hx
  have hx3 : w x<w x^3 := by nlinarith [sq_nonneg (w x-1)]
  have hlt : w (-(D*x))<w (x^3) := by
    rw [map_neg_eq_map,map_mul,map_pow]
    exact (mul_le_of_le_one_left (apply_nonneg w x) hD).trans_lt hx3
  have he : w y^2=w x^3 := by
    have hh := congrArg w hc
    rw [map_pow,sub_eq_add_neg,hna.add_eq_left_of_lt (map_neg_eq_map w) hlt,map_pow] at hh
    exact hh
  have hyp : 1<w y := by nlinarith [apply_nonneg w y,sq_nonneg (w y-1)]
  have hy : y≠0 := w.pos_iff.mp (lt_trans (by norm_num) hyp)
  have hxy : w x<w y := by
    have hxx : w x^2<w x^3 := by nlinarith [sq_pos_of_pos hxp]
    nlinarith [apply_nonneg w y]
  refine ⟨hy,hyp,?_,?_,?_⟩
  · rw [map_div₀,map_neg_eq_map]
    exact (div_lt_one (by positivity : 0<w y)).mpr hxy
  · rw [map_div₀,map_neg_eq_map,map_one]
    exact (div_lt_one (by positivity : 0<w y)).mpr hyp
  · field_simp [hy]
    linear_combination -hc

include hna in
/-- Converse: a nonzero small formal chart represents an actual x-pole. -/
lemma small_chart_to_pole (D z t:F) (hD:w D≤1) (hz:z≠0) (ht:t≠0)
    (hzs:w z<1) (hts:w t<1) (hc:t=z^3-D*z*t^2) : 1<w (z/t) := by
  have hu : w (1+D*z*t)=1 := one_add_unit w hna
    (small_mul w (small_mul w hD hzs).le hts)
  have he : t*(1+D*z*t)=z^3 := by linear_combination hc
  have hn := congrArg w he
  rw [map_mul,hu,mul_one,map_pow] at hn
  have hzp := w.pos hz
  have htp := w.pos ht
  have hpow : w z^3<w z := by
    have hs : w z^2< w z := by nlinarith
    nlinarith
  rw [map_div₀]
  apply (one_lt_div htp).mpr
  rwa [hn]

@[expose] def chordLambda (D z1 t1 z2 t2:F) : F :=
  (z1^2+z1*z2+z2^2-D*t2^2)/(1+D*z1*(t1+t2))
@[expose] def chordNu (D z1 t1 z2 t2:F) : F := t1-chordLambda D z1 t1 z2 t2*z1
@[expose] def chordQ (D z1 t1 z2 t2:F) : F := 1-D*(chordLambda D z1 t1 z2 t2)^2
@[expose] def thirdZ (D z1 t1 z2 t2:F) : F :=
  2*D*chordLambda D z1 t1 z2 t2*chordNu D z1 t1 z2 t2/chordQ D z1 t1 z2 t2-z1-z2
@[expose] def thirdT (D z1 t1 z2 t2:F) : F :=
  chordLambda D z1 t1 z2 t2*thirdZ D z1 t1 z2 t2+chordNu D z1 t1 z2 t2

include hna in
/-- All denominators are actual absolute-value units and every third-chart
coordinate remains small. The hypotheses do not exclude residue characteristic two. -/
lemma chord_small (D z1 t1 z2 t2:F) (hD:w D≤1)
    (hz1:w z1<1) (ht1:w t1<1) (hz2:w z2<1) (ht2:w t2<1) :
    w (1+D*z1*(t1+t2))=1 ∧ w (chordLambda D z1 t1 z2 t2)<1 ∧
    w (chordNu D z1 t1 z2 t2)<1 ∧ w (chordQ D z1 t1 z2 t2)=1 ∧
    w (thirdZ D z1 t1 z2 t2)<1 ∧ w (thirdT D z1 t1 z2 t2)<1 := by
  have hden : w (1+D*z1*(t1+t2))=1 := one_add_unit w hna
    (small_mul w (small_mul w hD hz1).le (small_add w hna ht1 ht2))
  have hnum : w (z1^2+z1*z2+z2^2-D*t2^2)<1 :=
    small_sub w hna (small_add w hna (small_add w hna (small_square w hz1) (small_mul w hz1.le hz2))
      (small_square w hz2)) (small_mul w hD (small_square w ht2))
  have hlam : w (chordLambda D z1 t1 z2 t2)<1 := by
    simpa only [chordLambda,map_div₀,hden,div_one] using hnum
  have hnu : w (chordNu D z1 t1 z2 t2)<1 :=
    small_sub w hna ht1 (small_mul w hlam.le hz1)
  have hq : w (chordQ D z1 t1 z2 t2)=1 :=
    one_sub_unit w hna (small_mul w hD (small_square w hlam))
  have h2 : w (2:F)≤1 := hna.apply_natCast_le_one (map_zero_le w 1) (map_one w)
  have h2D : w (2*D)≤1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg w D) h2).trans hD
  have hfrac : w (2*D*chordLambda D z1 t1 z2 t2*chordNu D z1 t1 z2 t2/chordQ D z1 t1 z2 t2)<1 := by
    rw [map_div₀,hq,div_one]
    exact small_mul w (small_mul w h2D hlam).le hnu
  have hz3 : w (thirdZ D z1 t1 z2 t2)<1 :=
    small_sub w hna (small_sub w hna hfrac hz1) hz2
  have ht3 : w (thirdT D z1 t1 z2 t2)<1 :=
    small_add w hna (small_mul w hlam.le hz3) hnu
  exact ⟨hden,hlam,hnu,hq,hz3,ht3⟩

#print axioms small_add
#print axioms small_sub
#print axioms small_mul
#print axioms small_square
#print axioms one_add_unit
#print axioms one_sub_unit
#print axioms affine_to_small_chart
#print axioms small_chart_to_pole
#print axioms chord_small
end FormalChartNorm
