module
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public section
namespace HCoefficients318

@[expose] def coefficient (j : ℕ) : ℚ :=
  ((2*j).choose j : ℚ) / ((4 : ℚ)^j * ((4*j+1 : ℕ) : ℚ))

theorem coefficient_ne_zero (j : ℕ) : coefficient j ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : j ≤ 2*j)))
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (by omega : 4*j+1 ≠ 0))

variable (p : ℕ) [Fact p.Prime]

theorem coefficient_valuation (hp : 19 ≤ p) (j : ℕ) :
    padicValRat p (coefficient j) =
      (padicValNat p ((2*j).choose j) : ℤ) - (padicValNat p (4*j+1) : ℤ) := by
  have hn : (((2*j).choose j : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : j ≤ 2*j)))
  have hd : (((4*j+1 : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (by omega : 4*j+1 ≠ 0)
  have h4 : ¬p ∣ 4 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0<4) h
    omega
  have hv4 : padicValRat p (4 : ℚ)=0 := by
    simpa only [Nat.cast_ofNat, padicValNat.eq_zero_of_not_dvd h4, Int.natCast_zero] using
      (padicValRat.of_nat (p:=p) (n:=4))
  rw [coefficient, padicValRat.div hn (mul_ne_zero (pow_ne_zero _ (by norm_num)) hd),
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hd, padicValRat.pow,
    hv4, mul_zero, zero_add, padicValRat.of_nat, padicValRat.of_nat]

theorem coefficient_valuation_lower (hp : 19 ≤ p) (j : ℕ) :
    -(Nat.log p (4*j+1) : ℤ) ≤ padicValRat p (coefficient j) := by
  rw [coefficient_valuation p hp]
  have h := padicValNat_le_nat_log (p:=p) (4*j+1)
  omega

theorem tail_denominator_lt_power (hp : 19 ≤ p) (k : ℕ) :
    4*(k+4)+1 < p^(k+1) := by
  induction k with
  | zero => simpa using (show 17<p by omega)
  | succ k ih =>
    calc
      4*(k+1+4)+1 < 19*(4*(k+4)+1) := by omega
      _ < 19*p^(k+1) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ ≤ p*p^(k+1) := Nat.mul_le_mul_right _ hp
      _ = p^(k+1+1) := by simp only [pow_succ]; ring

theorem tail_denominator_log (hp : 19 ≤ p) (k : ℕ) :
    Nat.log p (4*(k+4)+1) ≤ k := by
  have h := Nat.log_lt_of_lt_pow (by omega : 4*(k+4)+1≠0)
    (tail_denominator_lt_power p hp k)
  omega

theorem tail_coefficient_valuation (hp : 19 ≤ p) (k : ℕ) :
    -(k : ℤ) ≤ padicValRat p (coefficient (k+4)) := by
  have h := coefficient_valuation_lower p hp (k+4)
  have hl := tail_denominator_log p hp k
  omega

end HCoefficients318
#print axioms HCoefficients318.coefficient_valuation_lower
#print axioms HCoefficients318.tail_coefficient_valuation
