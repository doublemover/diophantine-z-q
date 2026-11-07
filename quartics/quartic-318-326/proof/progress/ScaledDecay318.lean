module
public import ScaledFormalSeries318
public import Mathlib.Analysis.SpecificLimits.Basic
public section
namespace ScaledDecay318
open ScaledCoefficients318 PowerSeries
variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- All indices, including the initial four, have denominator valuation at most j. -/
theorem denominator_lt_power (hp : 19 ≤ p) (j : ℕ) : 4*j+1 < p^(j+1) := by
  induction j with
  | zero => simpa using (show 1 < p by omega)
  | succ j ih =>
    calc
      4*(j+1)+1 < 19*(4*j+1) := by omega
      _ < 19*p^(j+1) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ ≤ p*p^(j+1) := Nat.mul_le_mul_right _ hp
      _ = p^(j+1+1) := by simp only [pow_succ]; ring

theorem h_coefficient_valuation (hp : 19 ≤ p) (j : ℕ) :
    -(j : ℤ) ≤ padicValRat p (HCoefficients318.coefficient j) := by
  have hv := HCoefficients318.coefficient_valuation_lower p hp j
  have hl := Nat.log_lt_of_lt_pow (by omega : 4*j+1 ≠ 0) (denominator_lt_power p hp j)
  omega

theorem h_cleared_one_norm (hp : 19 ≤ p) (j : ℕ) :
    ‖(HCoefficients318.coefficient j : ℚ_[p]) * (p : ℚ_[p])^j‖ ≤ 1 := by
  apply (Padic.norm_le_one_iff_val_nonneg _).2
  rw [Padic.valuation_mul
    (Rat.cast_ne_zero.mpr (HCoefficients318.coefficient_ne_zero j))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
    Padic.valuation_ratCast, Padic.valuation_pow, Padic.valuation_p, mul_one]
  have hv := h_coefficient_valuation p hp j
  omega

/-- Geometric decay survives at every integral argument, including units. -/
theorem hCoefficient_decay (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    ‖hCoefficient p D j‖ ≤ (‖(p : ℚ_[p])‖^3)^j := by
  have hd : ‖D^j‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hD
  have he : hCoefficient p D j =
      ((HCoefficients318.coefficient j : ℚ_[p]) * (p : ℚ_[p])^j) * D^j *
        (p : ℚ_[p])^(3*j) := by
    unfold hCoefficient
    rw [show 4*j=j+3*j by omega, pow_add]
    ring
  rw [he, norm_mul, norm_mul, norm_pow, ←pow_mul]
  have hm : ‖(HCoefficients318.coefficient j : ℚ_[p]) * (p : ℚ_[p])^j‖ * ‖D^j‖ ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul (h_cleared_one_norm p hp j) hd (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  simpa only [one_mul, norm_pow] using mul_le_mul_of_nonneg_right hm (pow_nonneg (norm_nonneg (p : ℚ_[p])) (3*j))

theorem bCoefficient_decay (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (j : ℕ) :
    ‖bCoefficient p D j‖ ≤ (‖(p : ℚ_[p])‖^4)^j := by
  have hd : ‖D^j‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hD
  unfold bCoefficient
  rw [norm_mul, norm_mul, norm_pow, ←pow_mul]
  have hm : ‖(FormalDifferential318.b j : ℚ_[p])‖ * ‖D^j‖ ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul (b_norm p hp j) hd (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  simpa only [one_mul, norm_pow] using mul_le_mul_of_nonneg_right hm (pow_nonneg (norm_nonneg (p : ℚ_[p])) (4*j))

theorem ratio_lt_one (k : ℕ) (hk : k ≠ 0) : ‖(p : ℚ_[p])‖^k < 1 :=
  pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one hk

/-- Actual convergence on the entire closed unit disc, not merely the maximal ideal. -/
theorem h_summable (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) :
    Summable (fun j : ℕ => hCoefficient p D j * t^j) := by
  refine (summable_geometric_of_lt_one (pow_nonneg (norm_nonneg _) 3)
    (ratio_lt_one p 3 (by decide))).of_norm_bounded fun j => ?_
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (‖(p : ℚ_[p])‖^3)^j * 1 := mul_le_mul (hCoefficient_decay p hp D hD j)
      (pow_le_one₀ (norm_nonneg _) ht) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := mul_one _

theorem b_summable (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1)
    (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) :
    Summable (fun j : ℕ => bCoefficient p D j * t^j) := by
  refine (summable_geometric_of_lt_one (pow_nonneg (norm_nonneg _) 4)
    (ratio_lt_one p 4 (by decide))).of_norm_bounded fun j => ?_
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (‖(p : ℚ_[p])‖^4)^j * 1 := mul_le_mul (bCoefficient_decay p hp D hD j)
      (pow_le_one₀ (norm_nonneg _) ht) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := mul_one _

/-- Same actual sum, now expressed through the constructed integral power series. -/
theorem Hscaled_summable (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (t : ℤ_[p]) :
    Summable (fun j : ℕ => coeff j (Hscaled p hp D hD) * t^j) := by
  refine (summable_geometric_of_lt_one (pow_nonneg (norm_nonneg (p : ℚ_[p])) 3)
    (ratio_lt_one p 3 (by decide))).of_norm_bounded fun j => ?_
  rw [←PadicInt.norm_coe]
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, coeff_Hscaled, coe_hIntegralCoefficient,
    norm_mul, norm_pow]
  calc
    _ ≤ (‖(p : ℚ_[p])‖^3)^j * 1 := mul_le_mul (hCoefficient_decay p hp D hD j)
      (pow_le_one₀ (norm_nonneg _) (by simpa only [PadicInt.norm_coe] using PadicInt.norm_le_one t))
      (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := mul_one _

theorem Bscaled_summable (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) (t : ℤ_[p]) :
    Summable (fun j : ℕ => coeff j (Bscaled p hp D hD) * t^j) := by
  refine (summable_geometric_of_lt_one (pow_nonneg (norm_nonneg (p : ℚ_[p])) 4)
    (ratio_lt_one p 4 (by decide))).of_norm_bounded fun j => ?_
  rw [←PadicInt.norm_coe]
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, coeff_Bscaled, coe_bIntegralCoefficient,
    norm_mul, norm_pow]
  calc
    _ ≤ (‖(p : ℚ_[p])‖^4)^j * 1 := mul_le_mul (bCoefficient_decay p hp D hD j)
      (pow_le_one₀ (norm_nonneg _) (by simpa only [PadicInt.norm_coe] using PadicInt.norm_le_one t))
      (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := mul_one _

end ScaledDecay318
#print axioms ScaledDecay318.h_coefficient_valuation
#print axioms ScaledDecay318.hCoefficient_decay
#print axioms ScaledDecay318.bCoefficient_decay
#print axioms ScaledDecay318.h_summable
#print axioms ScaledDecay318.b_summable
#print axioms ScaledDecay318.Hscaled_summable
#print axioms ScaledDecay318.Bscaled_summable
