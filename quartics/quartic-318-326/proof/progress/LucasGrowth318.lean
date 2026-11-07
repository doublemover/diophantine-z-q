module
public import LucasDivisibility318
public import SoundnessHeight318
public import Mathlib.Analysis.Complex.ExponentialBounds
public section
namespace LucasSequence318

 theorem log_six_lower : (3:ℝ)/2 < Real.log 6 := by
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have hsum : Real.log 6=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  linarith

/-- Exact Lucas growth for the literal integral residual. The sequence
classification and the index divisibility are proved by integer descent. -/
theorem literal_log_growth (s t z : ℤ) (hs : 7≤ |s|) (hz : z≠0)
    (heq : t^2-s*(s-2)*t*z+(s-2)^2*z^2=1) :
    |(s:ℝ)|-3<Real.log |(t:ℝ)| := by
  obtain ⟨m,hm,hpow⟩ := literal_growth s t z hs hz heq
  have hsR : (7:ℝ)≤ |(s:ℝ)| := by exact_mod_cast hs
  have hmR : |(s:ℝ)|-4≤(m:ℝ) := by exact_mod_cast hm
  have hpR : (|(s:ℝ)|-1)^m≤ |(t:ℝ)| := by exact_mod_cast hpow
  have hb : (0:ℝ)< |(s:ℝ)|-1 := by linarith
  have ht : (0:ℝ)< |(t:ℝ)| := (pow_pos hb m).trans_le hpR
  have hlog := Real.log_le_log (pow_pos hb m) hpR
  rw [Real.log_pow] at hlog
  have hbase : (3:ℝ)/2<Real.log (|(s:ℝ)|-1) :=
    log_six_lower.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hmul := mul_lt_mul_of_pos_left hbase (show (0:ℝ)<m by linarith)
  nlinarith only [hsR,hmR,hlog,hmul]

/-- The Lucas-growth comparison consumed by the final height separation. -/
theorem residual_log_growth (s t z : ℤ) (B : ℝ) (hs : 7≤ |s|) (hz : z≠0)
    (htB : |(t:ℝ)|≤B) (hres : HeightSeparation318.lucasResidual s t z=0) :
    |(s:ℝ)|-3<Real.log B := by
  have heq : t^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
    have hR : (t:ℝ)^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
      unfold HeightSeparation318.lucasResidual at hres
      linarith only [hres]
    exact_mod_cast hR
  have hg := literal_log_growth s t z hs hz heq
  have ht0 : t≠0 := by
    intro h
    subst t
    obtain ⟨m,hm,hpow⟩ := literal_growth s 0 z hs hz heq
    have hp : (0:ℤ)<(|s|-1)^m := pow_pos (by omega) m
    norm_num only [abs_zero] at hpow
    omega
  exact hg.trans_le (Real.log_le_log (abs_pos.mpr (by exact_mod_cast ht0)) htB)

/-- The actual anchor and scalar orientation supply the Lucas size threshold. -/
theorem anchor_orientation_large (a : ℤ) (c : ℝ)
    (horient : c=|(a:ℝ)-1| ∨ c=|(a:ℝ)+1|)
    (hanchor : 2*3^32767≤c) : 7≤|a| := by
  have hbinary := HeightSeparation318.anchor_binary_bound c hanchor
  have hp : (8:ℝ)≤2^49151 := by
    calc
      (8:ℝ)=2^3 := by norm_num
      _≤2^49151 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hsize := (HeightSeparation318.scalar_orientation_bounds a c horient).1
  have hc8 : (8:ℝ)<c := hp.trans_lt hbinary
  have hs : (7:ℝ)≤|(a:ℝ)| := by linarith only [hc8,hsize]
  exact_mod_cast hs

/-- The numerical separation theorem no longer requires a Lucas-growth
producer. The only analytical inputs are high, scalar and low heights. -/
theorem integer_input_from_three_height_comparisons
    (q : ℚ) (n a t z : ℤ) (B c : ℝ)
    (hn : Odd n) (hz : z≠0) (hB : 3≤B)
    (hnB : |(n:ℝ)|≤B) (haB : |(a:ℝ)|≤B)
    (htB : |(t:ℝ)|≤B) (hzB : |(z:ℝ)|≤B)
    (horient : c=|(a:ℝ)-1| ∨ c=|(a:ℝ)+1|)
    (hanchor : 2*3^32767≤c)
    (hhigh : HeightSeparation318.lucasResidual a t z≠0 → B^2-6 <
      7*HeightSeparation318.heightConstant*
        |HeightSeparation318.lucasResidual a t z|^((49:ℝ)/104))
    (hscalar : ZInQ.rationalLogHeight (3723*(2*q+1)^2)≤
      HeightSeparation318.heightConstant*c^((49:ℝ)/64))
    (hlow : 3723*(2*q+1)^2≠n → B^2-6 < 7*HeightSeparation318.heightConstant*
      (((3723*(2*q+1)^2-n).num.natAbs:ℝ)^((49:ℝ)/32))) :
    ∃ x:ℤ,(x:ℚ)=q := by
  exact HeightSeparation318.integer_input_from_height_and_group_data q n a t z B c
    hn hB hnB haB htB hzB horient hanchor hhigh
    (residual_log_growth a t z B (anchor_orientation_large a c horient hanchor) hz htB)
    hscalar hlow

end LucasSequence318
