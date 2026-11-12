module
public import ActualOddBadLocalRecurrence318
public section
noncomputable section
namespace ActualOddBadLocalDensity318
open Filter ActualFullLocalDensityRecurrence318 ActualOddBadLocalRecurrence318
open ActualLocalVolumeClosedForm318 ActualOriginalLocalDensityLimit318
open scoped Topology
set_option maxHeartbeats 28000000

@[expose] def badFactor (p : ℕ) : ℚ := ((p:ℚ)+1)^2/((p:ℚ)^2+p+1)
lemma actual_bad_fixed_point (p : ℕ) (hp : p.Prime) :
    primitiveFactor p+ratio p*badFactor p=badFactor p := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hpPos : (0:ℚ)<p := by exact_mod_cast hp.pos
  have hd : (p:ℚ)^2+p+1≠0 := ne_of_gt (by positivity)
  unfold primitiveFactor ratio badFactor
  field_simp [hp0,hd]
  <;> ring

/-- Both actual parity subsequences have their genuine, DIFFERENT
initial values. The prime-field bad-place count is not replaced by p^4. -/
theorem actual_bad_even_odd_formula (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (e : ℕ) :
    volume κ p (2*e)=badFactor p+(1-badFactor p)*ratio p^e ∧
    volume κ p (2*e+1)=badFactor p+(firstVolume p-badFactor p)*ratio p^e := by
  have hstep (n : ℕ) : volume κ p (n+2)=primitiveFactor p+ratio p*volume κ p n := by
    rw [actual_bad_volume_recurrence κ p hp hp2 hκ hκ2 n]
    simp only [ratio,div_eq_mul_inv,one_mul,mul_comm]
  induction e with
  | zero =>
    rw [mul_zero,zero_add,volume_zero,actual_bad_volume_one κ p hp hp2 hκ,pow_zero]
    constructor <;> ring
  | succ e ih =>
    have hE : 2*(e+1)=2*e+2 := by omega
    have hO : 2*e+2+1=(2*e+1)+2 := by omega
    simp only [hE,hO]
    rw [hstep,hstep,ih.1,ih.2,pow_succ (ratio p) e]
    have hf := actual_bad_fixed_point p hp
    constructor <;> nlinarith [hf]

/-- A genuine limit of ALL original local residue counts at an odd
prime of valuation one in kappa. Singular primitive classes that fail
modulo p^2 were removed by the explicit obstruction, not ignored. -/
theorem actual_bad_original_local_density (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) :
    Tendsto (fun n : ℕ => (volume κ p n:ℝ)) atTop (𝓝 (badFactor p:ℝ)) := by
  let C : ℝ := |1-(badFactor p:ℝ)|+|(firstVolume p:ℝ)-(badFactor p:ℝ)|
  have hr0 : (0:ℝ)≤(ratio p:ℝ) := by unfold ratio;positivity
  have hr1 : (ratio p:ℝ)<1 := by exact_mod_cast ratio_lt_one p hp
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp original_half_exponent_tendsto
  have hlim : Tendsto (fun n : ℕ => C*(ratio p:ℝ)^(n/2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hg
  have hbound (n : ℕ) : ‖(volume κ p n:ℝ)-(badFactor p:ℝ)‖≤C*(ratio p:ℝ)^(n/2) := by
    have hh := actual_bad_even_odd_formula κ p hp hp2 hκ hκ2 (n/2)
    have hc : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
    have hpow : (0:ℝ)≤(ratio p:ℝ)^(n/2) := pow_nonneg hr0 _
    rcases hc with he|ho
    · have heq := (congrArg (volume κ p) he).trans hh.1
      have her : (volume κ p n:ℝ)=(badFactor p:ℝ)+
          (1-(badFactor p:ℝ))*(ratio p:ℝ)^(n/2) := by
        rw [heq]
        simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_pow]
      rw [her,add_sub_cancel_left,Real.norm_eq_abs,abs_mul,abs_of_nonneg hpow]
      apply mul_le_mul_of_nonneg_right _ hpow
      dsimp [C]
      linarith [abs_nonneg ((firstVolume p:ℝ)-(badFactor p:ℝ))]
    · have heq := (congrArg (volume κ p) ho).trans hh.2
      have her : (volume κ p n:ℝ)=(badFactor p:ℝ)+
          ((firstVolume p:ℝ)-(badFactor p:ℝ))*(ratio p:ℝ)^(n/2) := by
        rw [heq]
        simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow]
      rw [her,add_sub_cancel_left,Real.norm_eq_abs,abs_mul,abs_of_nonneg hpow]
      apply mul_le_mul_of_nonneg_right _ hpow
      dsimp [C]
      linarith [abs_nonneg (1-(badFactor p:ℝ))]
  have hz : Tendsto (fun n : ℕ => (volume κ p n:ℝ)-(badFactor p:ℝ)) atTop (𝓝 0) :=
    squeeze_zero_norm hbound hlim
  simpa only [sub_add_cancel,zero_add] using hz.add_const (badFactor p:ℝ)

/-- Concrete odd bad places of the TWO ORIGINAL quartics. -/
theorem original_318_at_three :
    Tendsto (fun n : ℕ => (volume 318 3 n:ℝ)) atTop (𝓝 (16/13:ℝ)) := by
  convert actual_bad_original_local_density 318 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num [badFactor]
theorem original_318_at_fifty_three :
    Tendsto (fun n : ℕ => (volume 318 53 n:ℝ)) atTop (𝓝 (2916/2863:ℝ)) := by
  convert actual_bad_original_local_density 318 53 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num [badFactor]
theorem original_326_at_one_sixty_three :
    Tendsto (fun n : ℕ => (volume 326 163 n:ℝ)) atTop (𝓝 (26896/26733:ℝ)) := by
  convert actual_bad_original_local_density 326 163 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) using 1 <;> norm_num [badFactor]

end ActualOddBadLocalDensity318
