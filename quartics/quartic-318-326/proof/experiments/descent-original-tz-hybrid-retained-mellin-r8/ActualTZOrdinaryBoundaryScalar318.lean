module
public import Mathlib
public section
noncomputable section
namespace ActualTZOrdinaryBoundaryScalar318

@[expose] def envelope (k : ℕ) (R B : ℝ) : ℝ := (Real.log R*(2*R*B)^2)^k
@[expose] def short (n : ℝ) : ℝ := n^(-((1:ℝ)/4))

theorem inv_fine (n M d : ℝ) (hn : 1≤n) (hd : 0<d)
    (hM : d*n^((1:ℝ)/2)≤M) : 1/M≤(1/d)*short n := by
  have hN := zero_lt_one.trans_le hn
  have hNum : n^((1:ℝ)/4)≤n^((1:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hpos : 0<d*n^((1:ℝ)/4) := mul_pos hd (Real.rpow_pos_of_pos hN _)
  have hDen := (mul_le_mul_of_nonneg_left hNum hd.le).trans hM
  calc
    _ ≤ 1/(d*n^((1:ℝ)/4)) := div_le_div_of_nonneg_left zero_le_one hpos hDen
    _ = _ := by
      unfold short
      simp only [Real.rpow_neg hN.le,one_div,mul_inv]

/-- Discarded mass contributes uniformly once for the original
weight envelope and once for its missing center. -/
theorem lost_scalar (n M d C q : ℝ) (hn : 1≤n) (hd : 0<d) (hM : d*n^((1:ℝ)/2)≤M)
    (hC : 0≤C) (hq : 0≤q) :
    C*(short n+q/M)≤(C*(1+q/d))*short n := by
  have hh := mul_le_mul_of_nonneg_left (inv_fine n M d hn hd hM) hq
  have hh' : q/M≤(q/d)*short n := by
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using hh
  calc
    _ ≤ C*(short n+(q/d)*short n) := mul_le_mul_of_nonneg_left (add_le_add_left hh' _) hC
    _ = _ := by ring

/-- The actual signed CRT rounding loses only n^-3/4; the uniform
same-cutoff envelope already pays that, without a new power bound. -/
theorem interval_scalar (k : ℕ) (α R B n : ℝ) (hn : 1≤n) (hR : 1<R)
    (hα : 0≤α) (hα' : α≤1) (hB : 0≤B) :
    |(α*Real.log R)^k|*((((⌊R⌋₊+1:ℕ):ℝ))^(2*k)*(B^(2*k)/n^((3:ℝ)/4)))≤
      envelope k R B*short n := by
  have hL : 0≤Real.log R := Real.log_nonneg hR.le
  have hR₀ : 0≤R := zero_le_one.trans hR.le
  have hCut : (⌊R⌋₊:ℝ)+1≤2*R := by have h:=Nat.floor_le hR₀; linarith
  have hCap : ((⌊R⌋₊+1:ℕ):ℝ)≤2*R := by exact_mod_cast hCut
  have hαL : α*Real.log R≤Real.log R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hα' hL
  have hLogPow : |(α*Real.log R)^k|≤Real.log R^k := by
    rw [abs_of_nonneg (pow_nonneg (mul_nonneg hα hL) _)]
    exact pow_le_pow_left₀ (mul_nonneg hα hL) hαL _
  have hN : 0<n := zero_lt_one.trans_le hn
  have hp₄ := Real.rpow_pos_of_pos hN ((1:ℝ)/4)
  have hRatio : 1/n^((3:ℝ)/4)≤short n := by
    rw [short,Real.rpow_neg hN.le,←one_div]
    apply div_le_div_of_nonneg_left zero_le_one hp₄
    exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hLeft (u : ℝ) : Real.log R^k*((2*R)^(2*k)*(B^(2*k)*u))=envelope k R B*u := by
    calc
      _ = Real.log R^k*((2*R*B)^(2*k))*u := by rw [mul_pow (2*R) B]; ring
      _ = _ := by rw [envelope,mul_pow,←pow_mul]
  calc
    _ ≤ Real.log R^k*((2*R)^(2*k)*(B^(2*k)/n^((3:ℝ)/4))) := by
      have hPP : 0≤B^(2*k)/n^((3:ℝ)/4) := by positivity
      exact mul_le_mul hLogPow
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hCap _) hPP)
        (by positivity) (pow_nonneg hL _)
    _ ≤ Real.log R^k*((2*R)^(2*k)*(B^(2*k)*short n)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL _)
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hRatio) (pow_nonneg hB _)
    _ = _ := hLeft _

end ActualTZOrdinaryBoundaryScalar318
