module
public import ActualTZLowFrequencyPole318
public section
noncomputable section
namespace ActualTZHighBandPower318
open ActualTZLowFrequencyPole318

/-- Same H=L^(1/4), with an integer Schwartz moment of order
4(k+D+2). No change to the true angular cutoff. -/
theorem high_power (L : ℝ) (hL : 1≤L) (k D : ℕ) :
    L^k*(1+L)^D*(band L^(4*(k+D+2)))⁻¹≤(2:ℝ)^D/L^2 := by
  have hp : 0<L := zero_lt_one.trans_le hL
  have hL0 : 0≤L := hp.le
  have h4 : band L^4=L := by
    rw [band,←Real.rpow_natCast,←Real.rpow_mul hL0]
    norm_num [Real.rpow_one]
  have hh : band L^(4*(k+D+2))=L^(k+D+2) := by rw [pow_mul,h4]
  have hD : (1+L)^D≤(2*L)^D :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ L^k*(2*L)^D*(band L^(4*(k+D+2)))⁻¹ := by
      have hb : 0≤band L := Real.rpow_nonneg hL0 _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by positivity)) (by positivity)
    _ = _ := by
      rw [hh,mul_pow,pow_add L (k+D) 2,pow_add L k D]
      field_simp [hp.ne',pow_ne_zero k hp.ne',pow_ne_zero D hp.ne'] <;> ring

end ActualTZHighBandPower318
