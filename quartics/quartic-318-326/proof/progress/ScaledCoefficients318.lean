module
public import GenericFormalDifferential318
public import JTail318
public import Mathlib.NumberTheory.Padics.PadicIntegers
public section

namespace ScaledCoefficients318
open PowerSeries
variable (p : ℕ) [Fact p.Prime]

/-- Clearing by p^(4j) makes every actual coefficient of H integral. -/
theorem h_cleared_norm (hp : 19 ≤ p) (j : ℕ) :
    ‖(HCoefficients318.coefficient j : ℚ_[p]) * (p : ℚ_[p])^(4*j)‖ ≤ 1 := by
  apply (Padic.norm_le_one_iff_val_nonneg _).2
  rw [Padic.valuation_mul
    (Rat.cast_ne_zero.mpr (HCoefficients318.coefficient_ne_zero j))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
    Padic.valuation_ratCast, Padic.valuation_pow, Padic.valuation_p, mul_one]
  have hv := HCoefficients318.coefficient_valuation_lower p hp j
  have hl := Nat.log_lt_self p (by omega : 4*j+1 ≠ 0)
  omega

/-- The exact scaled H coefficient, with no condition excluding D=0. -/
@[expose] noncomputable def hCoefficient (D : ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  (HCoefficients318.coefficient j : ℚ_[p]) * D^j * (p : ℚ_[p])^(4*j)

/-- The exact scaled central-binomial coefficient. -/
@[expose] noncomputable def bCoefficient (D : ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  (FormalDifferential318.b j : ℚ_[p]) * D^j * (p : ℚ_[p])^(4*j)

theorem hCoefficient_norm (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    ‖hCoefficient p D j‖ ≤ 1 := by
  have hpow : ‖D^j‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hD
  unfold hCoefficient
  rw [mul_right_comm, norm_mul]
  calc
    _ ≤ 1 * ‖D^j‖ := mul_le_mul_of_nonneg_right (h_cleared_norm p hp j) (norm_nonneg _)
    _ ≤ 1 := by simpa using hpow

theorem b_norm (hp : 19 ≤ p) (j : ℕ) :
    ‖(FormalDifferential318.b j : ℚ_[p])‖ ≤ 1 := by
  have h4 : ‖(4 : ℚ_[p])‖ = 1 := by
    simpa using JTail318.norm_nat_unit p 4 (by decide) (by omega)
  simp only [FormalDifferential318.b, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, norm_div, norm_pow, h4, one_pow, div_one]
  exact JTail318.norm_nat_le_one p _

theorem bCoefficient_norm (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    ‖bCoefficient p D j‖ ≤ 1 := by
  have hd : ‖D^j‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hD
  have hpj : ‖(p : ℚ_[p])^(4*j)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (Padic.norm_p_lt_one.le)
  unfold bCoefficient
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (1 * 1) * 1 := mul_le_mul
      (mul_le_mul (b_norm p hp j) hd (norm_nonneg _) (by norm_num))
      hpj (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

@[expose] noncomputable def hIntegralCoefficient (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (j : ℕ) : ℤ_[p] := (hCoefficient p D j).lift (hCoefficient_norm p hp D hD j)

@[expose] noncomputable def bIntegralCoefficient (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (j : ℕ) : ℤ_[p] := (bCoefficient p D j).lift (bCoefficient_norm p hp D hD j)

@[expose] noncomputable def Hscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries ℤ_[p] := PowerSeries.mk (hIntegralCoefficient p hp D hD)

@[expose] noncomputable def Bscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries ℤ_[p] := PowerSeries.mk (bIntegralCoefficient p hp D hD)

@[simp] theorem coe_hIntegralCoefficient (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (j : ℕ) : (hIntegralCoefficient p hp D hD j : ℚ_[p]) = hCoefficient p D j := rfl

@[simp] theorem coe_bIntegralCoefficient (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (j : ℕ) : (bIntegralCoefficient p hp D hD j : ℚ_[p]) = bCoefficient p D j := rfl

@[simp] theorem coeff_Hscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    coeff j (Hscaled p hp D hD) = hIntegralCoefficient p hp D hD j := coeff_mk _ _

@[simp] theorem coeff_Bscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    coeff j (Bscaled p hp D hD) = bIntegralCoefficient p hp D hD j := coeff_mk _ _

/-- Exact coefficientwise binding to the original rational H series. -/
theorem map_Hscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (Hscaled p hp D hD).map PadicInt.Coe.ringHom =
      rescale (D * (p : ℚ_[p])^4) (GenericFormalDifferential318.H (K := ℚ_[p])) := by
  ext j
  simp only [coeff_map, coeff_Hscaled, PadicInt.Coe.ringHom_apply,
    coe_hIntegralCoefficient, coeff_rescale, GenericFormalDifferential318.H,
    FormalDifferential318.coeff_H, Rat.coe_castHom, hCoefficient, mul_pow, ←pow_mul]
  ring

/-- Exact coefficientwise binding to the original rational binomial series. -/
theorem map_Bscaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (Bscaled p hp D hD).map PadicInt.Coe.ringHom =
      rescale (D * (p : ℚ_[p])^4) (GenericFormalDifferential318.B (K := ℚ_[p])) := by
  ext j
  simp only [coeff_map, coeff_Bscaled, PadicInt.Coe.ringHom_apply,
    coe_bIntegralCoefficient, coeff_rescale, GenericFormalDifferential318.B,
    FormalDifferential318.coeff_B, Rat.coe_castHom, bCoefficient, mul_pow, ←pow_mul]
  ring

end ScaledCoefficients318

#print axioms ScaledCoefficients318.h_cleared_norm
#print axioms ScaledCoefficients318.hCoefficient_norm
#print axioms ScaledCoefficients318.b_norm
#print axioms ScaledCoefficients318.bCoefficient_norm
#print axioms ScaledCoefficients318.map_Hscaled
#print axioms ScaledCoefficients318.map_Bscaled
