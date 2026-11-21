module
public import ActualTZOrdinaryNumericDensity318
public section
noncomputable section
namespace ActualTZOrdinaryFineRemainder318
open Filter Asymptotics
open scoped Topology
open ActualTZOrdinaryNumericDensity318

@[expose] def fineEnvelope (d x : ℝ) : ℝ :=
  ((2:ℝ)^((1:ℝ)/4)*Real.exp 1/d)*((Real.log 3+Real.log x)*x^(-((1:ℝ)/4)))

theorem pointwise (N : ℕ) (hN : 0<N) (d M : ℝ) (hd : 0<d)
    (hM : d*(N:ℝ)^((1:ℝ)/2)≤M) : Fbound N M≤fineEnvelope d N := by
  have hN₁ : (1:ℝ)≤N := by exact_mod_cast (show 1≤N from hN)
  have hN₀ := zero_lt_one.trans_le hN₁
  have hT : 0<(2*(N:ℝ)+1) := by positivity
  have hT₁ : 1≤2*(N:ℝ)+1 := by linarith
  have hc := Real.log_le_sub_one_of_pos hT
  have hl₁ : 0≤Real.log (2*(N:ℝ)+1) := Real.log_nonneg hT₁
  have hLog : Real.log (1+Real.log (2*(N:ℝ)+1))≤Real.log 3+Real.log (N:ℝ) := by
    calc
      _ ≤ Real.log (2*(N:ℝ)+1) := Real.log_le_log (by positivity) (by linarith)
      _ ≤ Real.log (3*(N:ℝ)) := Real.log_le_log hT (by linarith)
      _ = _ := Real.log_mul (by norm_num) hN₀.ne'
  have hD : 0<d*(N:ℝ)^((1:ℝ)/2) := mul_pos hd (Real.rpow_pos_of_pos hN₀ _)
  have hA : 0≤(2*(N:ℝ))^((1:ℝ)/4)*Real.exp 1 := by positivity
  have hp : (N:ℝ)^((1:ℝ)/4)/(N:ℝ)^((1:ℝ)/2)=(N:ℝ)^(-((1:ℝ)/4)) := by
    rw [←Real.rpow_sub hN₀]
    norm_num
  unfold Fbound
  push_cast
  calc
    _ ≤ (2*(N:ℝ))^((1:ℝ)/4)*(Real.exp 1*Real.log (1+Real.log (2*(N:ℝ)+1)))/
        (d*(N:ℝ)^((1:ℝ)/2)) :=
      div_le_div_of_nonneg_left (by positivity) hD hM
    _ ≤ (2*(N:ℝ))^((1:ℝ)/4)*(Real.exp 1*(Real.log 3+Real.log (N:ℝ)))/
        (d*(N:ℝ)^((1:ℝ)/2)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hLog hA
    _ = _ := by
      unfold fineEnvelope
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hN₀.le,←hp]
      have hpow := (Real.rpow_pos_of_pos hN₀ ((1:ℝ)/2)).ne'
      field_simp [hd.ne',hpow] <;> ring

theorem fine_tendsto (d : ℝ) : Tendsto (fineEnvelope d) atTop (𝓝 0) := by
  have hp := _root_.tendsto_rpow_neg_atTop (show (0:ℝ)<(1:ℝ)/4 by norm_num)
  have h₁ : Tendsto (fun x : ℝ=>Real.log x*x^(-((1:ℝ)/4))) atTop (𝓝 0) := by
    have H := (_root_.isLittleO_log_rpow_rpow_atTop (1:ℝ)
      (show (0:ℝ)<(1:ℝ)/4 by norm_num)).tendsto_div_nhds_zero
    refine H.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [Real.rpow_one,div_eq_mul_inv,Real.rpow_neg (zero_le_one.trans hx)]
  have h₂ := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ=>Real.log 3) atTop (𝓝 (Real.log 3))).mul hp
  have h₃ := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ=>(2:ℝ)^((1:ℝ)/4)*Real.exp 1/d) atTop
      (𝓝 ((2:ℝ)^((1:ℝ)/4)*Real.exp 1/d))).mul (h₂.add h₁)
  simpa only [fineEnvelope,add_mul,mul_zero,add_zero] using h₃

end ActualTZOrdinaryFineRemainder318
