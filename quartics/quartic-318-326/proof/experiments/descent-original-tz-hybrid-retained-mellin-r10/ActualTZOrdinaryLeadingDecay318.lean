module
public import ActualTZOrdinaryNumericDensity318
public section
noncomputable section
namespace ActualTZOrdinaryLeadingDecay318
open Filter Asymptotics
open scoped Topology
open ActualTZOrdinaryNumericDensity318 ActualTZPhysicalCorrectionBound318

/-- The finite constants can be chosen from the old shape once.
This is true outer y-decay, not an assertion of a fixed-y o(1). -/
theorem leading_tendsto (k : ℕ) (A C : ℝ) :
    Tendsto (leading k A C) atTop (𝓝 0) := by
  have hNat : Tendsto (fun y : ℕ=>(y:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℝ=>x⁻¹) atTop (𝓝 0) := by
    simpa only [Real.rpow_neg_one] using
      (_root_.tendsto_rpow_neg_atTop (show (0:ℝ)<1 by norm_num))
  have hLog : Tendsto (fun y : ℕ=>(Real.log (y:ℝ))⁻¹) atTop (𝓝 0) :=
    hinv.comp (Real.tendsto_log_atTop.comp hNat)
  have hInv := hinv.comp hNat
  have hG : Tendsto (Gbound k A) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>goodConst k) atTop (𝓝 (goodConst k))).mul hInv
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>badConst k*A) atTop (𝓝 (badConst k*A))).mul hLog
    simpa only [Gbound,div_eq_mul_inv,mul_assoc,mul_zero,add_zero] using h₁.add h₂
  have he₀ : Tendsto Real.exp (𝓝 0) (𝓝 (Real.exp 0)) := Real.continuous_exp.continuousAt
  have he : Tendsto (fun y=>Real.exp (Gbound k A y)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero] using he₀.comp hG
  have hY : Tendsto tailY atTop (𝓝 0) := by
    have h := (_root_.tendsto_rpow_neg_atTop (show (0:ℝ)<(3:ℝ)/4 by norm_num)).comp hNat
    simpa only [tailY,div_eq_mul_inv,zero_mul] using h.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(((3:ℝ)/4)⁻¹)) atTop (𝓝 (((3:ℝ)/4)⁻¹)))
  have hM := (he.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℕ=>multiplier k C) atTop (𝓝 (multiplier k C)))).mul hY
  have hOne := he.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1))
  simpa only [leading,sub_self,mul_zero,zero_add] using hOne.add hM

theorem leading_nonneg (k : ℕ) (A C : ℝ) (y : ℕ) (hA : 0≤A) (hC : 0≤C) (hY : 1<y) :
    0≤leading k A C y := by
  have hlog : 0≤Real.log y := Real.log_nonneg (by exact_mod_cast hY.le)
  have hG : 0≤Gbound k A y := by
    unfold Gbound
    exact add_nonneg (div_nonneg (good_nonnegative k) (by positivity))
      (mul_nonneg (bad_nonnegative k) (div_nonneg hA hlog))
  have hE : 0≤Real.exp (Gbound k A y)-1 := by
    exact sub_nonneg.mpr (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hG)
  unfold leading multiplier tailY
  have hc := bad_nonnegative k
  exact add_nonneg hE (by positivity)

end ActualTZOrdinaryLeadingDecay318
