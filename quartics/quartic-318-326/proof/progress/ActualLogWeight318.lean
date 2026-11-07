module
public import Contact49Growth318
public section
noncomputable section
namespace ActualLogWeight318
set_option maxHeartbeats 0

@[expose] def C : ℝ := 210^300

theorem C_pos : 0<C := by unfold C; positivity

theorem log_C_lt : Real.log C<1800 := by
  have h210 := Real.log_lt_log (by norm_num : (0:ℝ)<210) (by norm_num : (210:ℝ)<2^8)
  rw [Real.log_pow] at h210
  have h6 : Real.log (210:ℝ)<6 := by norm_num only [Nat.cast_ofNat] at h210; linarith [Real.log_two_lt_d9]
  unfold C
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem log_six_lt_two : Real.log (6:ℝ)<2 := by
  rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_lt_d9,Real.log_three_lt_d9]

/-- The actual logarithm in the adopted source, with its literal fixed constant. -/
theorem log_level_bound (R d N : ℝ) (hR : 1≤R) (hd0 : 0<d) (hN0 : 0<N)
    (hd : d<2^14*C*R^((97:ℝ)/32)) (hN : N≤C*R^2) :
    Real.log (6*d*N)<4096+6*Real.log R := by
  have hR0 : 0<R := by linarith
  have hCp := C_pos
  have hdl := Real.log_lt_log hd0 hd
  have hNl := Real.log_le_log hN0 hN
  rw [Real.log_mul (mul_ne_zero (by positivity) hCp.ne') (Real.rpow_pos_of_pos hR0 _).ne',
    Real.log_mul (by positivity) hCp.ne',Real.log_pow,Real.log_rpow hR0] at hdl
  rw [Real.log_mul hCp.ne' (pow_ne_zero 2 hR0.ne'),Real.log_pow] at hNl
  rw [Real.log_mul (mul_ne_zero (by norm_num) hd0.ne') hN0.ne',
    Real.log_mul (by norm_num) hd0.ne']
  norm_num only [Nat.cast_ofNat] at hdl hNl
  have hr := Real.log_nonneg hR
  linarith [log_C_lt,log_six_lt_two,Real.log_two_lt_d9]

theorem actual_log_weight (R d N : ℝ) (hR : 1≤R) (hd0 : 0<d) (hN0 : 0<N)
    (hd : d<2^14*C*R^((97:ℝ)/32)) (hN : N≤C*R^2) :
    Real.log (6*d*N)<2^13*R^((1:ℝ)/32) :=
  (log_level_bound R d N hR hd0 hN0 hd hN).trans (Contact49Growth318.log_weight_bound R hR)

theorem log_level_ge_one (d N : ℝ) (hd : 1≤d) (hN : 1≤N) : 1≤Real.log (6*d*N) := by
  have hp : (6:ℝ)≤6*d*N := by nlinarith [mul_le_mul hd hN (by norm_num) (by linarith : 0≤d)]
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<6) hp
  have h6 : Real.log (6:ℝ)=Real.log 2+Real.log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  rw [h6] at hl
  linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]

/-- Exact binding of the finite growth certificate to the actual log(6dN). -/
theorem actual_jacobian_growth (R d N h : ℝ) (hR : 1≤R) (hd0 : 1≤d) (hN0 : 1≤N)
    (hd : d<2^14*C*R^((97:ℝ)/32)) (hN : N≤C*R^2)
    (hh : h≤2^11*d^2*(Real.log (6*d*N))^2) :
    h<2^65*C^2*R^((49:ℝ)/8) :=
  Contact49Growth318.jacobian_growth R C d _ h hR C_pos (by linarith)
    (by linarith [log_level_ge_one d N hd0 hN0]) hd
    (actual_log_weight R d N hR (by linarith) (by linarith) hd hN) hh

end ActualLogWeight318
#print axioms ActualLogWeight318.log_level_bound
#print axioms ActualLogWeight318.actual_log_weight
#print axioms ActualLogWeight318.actual_jacobian_growth
