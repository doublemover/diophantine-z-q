module
public import ActualOriginalDyadicBaseCount318
public section
noncomputable section
namespace ActualOriginalDyadicPrimitiveCount318
open ActualOddRegularResidueTower318 ActualDyadicRegularRecurrence318
open ActualOriginalDyadicBaseCount318 ActualPrimitivePrimePower318
set_option maxHeartbeats 28000000

/-- The actual finite mod8 base and constructed original dyadic
involution count every regular residue at every subsequent level. -/
theorem actual_regular_all_dyadic_levels (κ : ℤ) (hκ8 : (κ:ZMod 8)=6) (e : ℕ) :
    Nat.card (RegularResidues κ (2^(e+3)) 2)=4096*16^e := by
  induction e with
  | zero => simpa only [zero_add,show (2:ℕ)^3=8 by norm_num,pow_zero,mul_one] using
      actual_original_regular_eight_count κ hκ8
  | succ e ih =>
    have he : e+1+3=e+4 := by omega
    rw [he,actual_dyadic_regular_prime_power_step,ih,pow_succ 16 e]
    exact mul_assoc _ _ _

/-- At the original valuation-one dyadic place, primitivity coincides
with regularity above modulus4 by the integer nonlifting obstruction. -/
theorem actual_primitive_all_dyadic_levels (κ : ℤ) (hκ : (2:ℤ)∣κ) (hκ4 : ¬(2:ℤ)^2∣κ)
    (hκ8 : (κ:ZMod 8)=6) (e : ℕ) :
    Nat.card (PrimitiveResidues κ (2^(e+3)) 2)=2^(4*(e+3)) := by
  have hd : (2:ℕ)^2∣2^(e+3) := by
    refine ⟨2^(e+1),?_⟩
    rw [show e+3=2+(e+1) by omega,pow_add]
  rw [Nat.card_congr (actual_primitive_regular_equiv κ (2^(e+3)) 2 (by norm_num) hκ hκ4 hd),
    actual_regular_all_dyadic_levels κ hκ8 e]
  rw [show 4*(e+3)=4*e+12 by omega,pow_add,pow_mul]
  norm_num only [show (2:ℕ)^4=16 by norm_num,show (2:ℕ)^12=4096 by norm_num]
  exact mul_comm _ _

/-- The original dyadic primitive volume is exactly1, not the
inapplicable good-prime factor15/16. -/
theorem actual_dyadic_primitive_volume (κ : ℤ) (hκ : (2:ℤ)∣κ) (hκ4 : ¬(2:ℤ)^2∣κ)
    (hκ8 : (κ:ZMod 8)=6) (e : ℕ) :
    (Nat.card (PrimitiveResidues κ (2^(e+3)) 2):ℚ)/(2:ℚ)^(4*(e+3))=1 := by
  rw [actual_primitive_all_dyadic_levels κ hκ hκ4 hκ8 e,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (pow_ne_zero _ (by norm_num))

end ActualOriginalDyadicPrimitiveCount318
