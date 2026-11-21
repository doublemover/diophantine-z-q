module
public import Mathlib
public section
noncomputable section
namespace ActualA4CofinalIntegerScale318

open Filter Asymptotics
open scoped Topology

@[expose] def scaleB (a t : ℕ) := t^(40*a)
@[expose] def scaleY (a t : ℕ) := t^(2*a)
@[expose] def scaleZ (a t : ℕ) := t^a

/-- Using an integer-power cofinal subsequence eliminates all square-root
and cutoff floor losses. FT's eventual lower permits this exact scale. -/
theorem crt_range (a t : ℕ) (ht : 1 ≤ t) :
    scaleY a t*(scaleZ a t)^2 ≤ scaleB a t := by
  rw [scaleY,scaleZ,scaleB,←pow_mul,←pow_add]
  apply pow_right_mono₀ ht
  omega

theorem t_le_Y (a t : ℕ) (ha : 0 < a) (ht : 1 ≤ t) : t ≤ scaleY a t := by
  conv_lhs => rw [←pow_one t]
  exact pow_right_mono₀ ht (by omega : 1 ≤ 2*a)

theorem t_le_B (a t : ℕ) (ha : 0 < a) (ht : 1 ≤ t) : t ≤ scaleB a t := by
  conv_lhs => rw [←pow_one t]
  exact pow_right_mono₀ ht (by omega : 1 ≤ 40*a)

theorem t_sq_le_B_sq (a t : ℕ) (ha : 0 < a) (ht : 1 ≤ t) :
    t^2 ≤ (scaleB a t)^2 := pow_le_pow_left₀ (zero_le _) (t_le_B a t ha ht) 2

theorem log_N (a t : ℕ) :
    Real.log (((scaleB a t:ℕ):ℝ)^2) = (80*(a:ℝ))*Real.log (t:ℝ) := by
  rw [scaleB,Nat.cast_pow,←pow_mul,Real.log_pow]
  push_cast
  ring

theorem logY_ge (a t : ℕ) (ha : 0 < a) (ht : 2 ≤ t) :
    Real.log 2 ≤ Real.log (scaleY a t:ℝ) :=
  Real.log_le_log (by norm_num) (by exact_mod_cast ht.trans (t_le_Y a t ha (by omega)))

@[expose] def remainderRatio (a r t : ℕ) : ℝ :=
  (Real.log (((scaleB a t:ℕ):ℝ)^2))^r*
      (((scaleZ a t:ℕ):ℝ)^6)*(scaleY a t+1:ℕ)/(scaleB a t:ℝ)

@[expose] def largeRatio (a r t : ℕ) : ℝ :=
  (Real.log (((scaleB a t:ℕ):ℝ)^2))^r/
      ((scaleY a t:ℝ)*Real.log (scaleY a t:ℝ))

private theorem scale_square (a t : ℕ) (ha : 0 < a) (ht : 1 ≤ t) :
    ((scaleZ a t:ℕ):ℝ)^6*(scaleY a t:ℝ)*(t:ℝ) ≤ (scaleB a t:ℝ) := by
  have ht' : (1:ℝ)≤t := by exact_mod_cast ht
  simp only [scaleZ,scaleY,scaleB,Nat.cast_pow,←pow_mul]
  conv_lhs => rhs; rw [←pow_one (t:ℝ)]
  rw [←pow_add,←pow_add]
  exact pow_right_mono₀ ht' (by omega)

theorem ratios (a r t : ℕ) (ha : 0 < a) (ht : 2 ≤ t) :
    remainderRatio a r t ≤ 2*(80*(a:ℝ))^r*((Real.log (t:ℝ))^r/(t:ℝ)) ∧
    largeRatio a r t ≤ (80*(a:ℝ))^r/Real.log 2*((Real.log (t:ℝ))^r/(t:ℝ)) := by
  have ht0 : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have ht1 : 1 ≤ t := by omega
  have hy0 : (0:ℝ)<scaleY a t := by
    exact_mod_cast (lt_of_lt_of_le (show 0<t by omega) (t_le_Y a t ha ht1))
  have hb0 : (0:ℝ)<scaleB a t := by
    exact_mod_cast (lt_of_lt_of_le (show 0<t by omega) (t_le_B a t ha ht1))
  let L := (80*(a:ℝ))^r*((Real.log (t:ℝ))^r)
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg (by positivity) (pow_nonneg (Real.log_nonneg (by exact_mod_cast ht1)) _)
  have hMain : (Real.log (((scaleB a t:ℕ):ℝ)^2))^r=L := by
    rw [log_N,mul_pow]
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  constructor
  · rw [remainderRatio,hMain]
    have hy : (1:ℝ) ≤ (scaleY a t:ℝ) := by exact_mod_cast ht1.trans (t_le_Y a t ha ht1)
    have hyd : ((scaleY a t+1:ℕ):ℝ) ≤ 2*(scaleY a t:ℝ) := by push_cast; linarith
    have H :
        (((scaleZ a t:ℕ):ℝ)^6*((scaleY a t+1:ℕ):ℝ))*(t:ℝ) ≤ 2*(scaleB a t:ℝ) := by
      have hu := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hyd (pow_nonneg (Nat.cast_nonneg _) 6)) ht0.le
      have hv := mul_le_mul_of_nonneg_left (scale_square a t ha ht1) (by norm_num : (0:ℝ)≤2)
      exact hu.trans (by convert hv using 1 <;> ring)
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hb0 ht0).2
    have H' := mul_le_mul_of_nonneg_left H hL
    convert H' using 1 <;> dsimp only [L] <;> ring
  · rw [largeRatio,hMain]
    have hY : (t:ℝ) ≤ scaleY a t := by exact_mod_cast t_le_Y a t ha ht1
    have hP := mul_le_mul hY (logY_ge a t ha ht) h2.le hy0.le
    have hP0 : 0 < (t:ℝ)*Real.log 2 := mul_pos ht0 h2
    have H := div_le_div_of_nonneg_left hL hP0 hP
    convert H using 1 <;> dsimp only [L] <;> ring

/-- Ordinary log powers lose to t, so both normalized errors vanish on
the integer cofinal scales. No arithmetic-distribution hypothesis. -/
theorem eventual_small (a r : ℕ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, 2 ≤ t ∧ remainderRatio a r t ≤ ε ∧ largeRatio a r t ≤ ε := by
  have H0 := (_root_.isLittleO_log_rpow_rpow_atTop (r:ℝ) (by norm_num : 0<(1:ℝ))).tendsto_div_nhds_zero
  have H : Tendsto (fun t : ℕ => (Real.log (t:ℝ))^r/(t:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,Real.rpow_one,Function.comp_apply] using
      H0.comp (tendsto_natCast_atTop_atTop : Tendsto (fun t : ℕ => (t:ℝ)) atTop atTop)
  let C : ℝ := max (2*(80*(a:ℝ))^r) ((80*(a:ℝ))^r/Real.log 2)
  have hC : 0 < C := by
    have haR : (0:ℝ)<a := by exact_mod_cast ha
    exact (show 0 < 2*(80*(a:ℝ))^r by positivity).trans_le (le_max_left _ _)
  have hEv : ∀ᶠ t : ℕ in atTop, (Real.log (t:ℝ))^r/(t:ℝ) < ε/C :=
    H.eventually_lt_const (div_pos hε hC)
  obtain ⟨t0,h0⟩ := eventually_atTop.mp (hEv.and (eventually_ge_atTop (2:ℕ)))
  refine ⟨t0,?_⟩
  intro t ht
  obtain ⟨hT,htwo⟩ := h0 t ht
  have hnn : 0≤(Real.log (t:ℝ))^r/(t:ℝ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤t by omega))) _) (Nat.cast_nonneg _)
  have hCprod : C*((Real.log (t:ℝ))^r/(t:ℝ)) ≤ ε := by
    have hh := (lt_div_iff₀ hC).mp hT
    simpa only [mul_comm] using hh.le
  obtain ⟨hE,hG⟩ := ratios a r t ha htwo
  exact ⟨htwo,hE.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hnn).trans hCprod),
    hG.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) hnn).trans hCprod)⟩

end ActualA4CofinalIntegerScale318
