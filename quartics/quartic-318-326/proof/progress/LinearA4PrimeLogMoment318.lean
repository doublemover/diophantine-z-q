module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public section
noncomputable section

/-! The first logarithmic prime moment needed for the rank-r original
Gaussian Selberg denominator. The estimate uses the actual Mathlib
Chebyshev upper bound; neither a prime number theorem nor an unproved
prime-moment hypothesis is needed for this part. -/
namespace LinearA4PrimeLogMoment318
open scoped BigOperators

def moment (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, Real.log (p:ℝ)/(p:ℝ)

theorem prime_log_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log (p:ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

theorem monotone_moment : Monotone moment := by
  intro a b h
  unfold moment
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono h)
  intro p hp _
  exact div_nonneg (prime_log_nonneg (Nat.mem_primesLE.mp hp).2) (by positivity)

theorem shell (k : ℕ) :
    (∑ p ∈ Nat.primesLE (2^(k+1)) \ Nat.primesLE (2^k),
      Real.log (p:ℝ)/(p:ℝ)) ≤ 2*Real.log 4 := by
  let S := Nat.primesLE (2^(k+1)) \ Nat.primesLE (2^k)
  have hK : 0 < (2:ℝ)^k := by positivity
  change (∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) ≤ _
  calc
    _ ≤ ∑ p ∈ S, Real.log (p:ℝ)/(2:ℝ)^k := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_sdiff.mp hp
      have hprime := (Nat.mem_primesLE.mp hmem.1).2
      have hpK : 2^k < p :=
        lt_of_not_ge (fun e => hmem.2 (Nat.mem_primesLE.mpr ⟨e,hprime⟩))
      exact div_le_div_of_nonneg_left (prime_log_nonneg hprime) hK
        (by exact_mod_cast hpK.le)
    _ = (∑ p ∈ S, Real.log (p:ℝ))/(2:ℝ)^k := by
      rw [Finset.sum_div]
    _ ≤ Chebyshev.theta (((2:ℕ)^(k+1):ℕ):ℝ)/(2:ℝ)^k := by
      apply div_le_div_of_nonneg_right _ hK.le
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun p hp _ => prime_log_nonneg (Nat.mem_primesLE.mp hp).2)
    _ ≤ (Real.log 4 * ((2:ℕ)^(k+1):ℕ))/(2:ℝ)^k := by
      exact div_le_div_of_nonneg_right
        (Chebyshev.theta_le_log4_mul_x (by positivity)) hK.le
    _ = 2*Real.log 4 := by
      push_cast
      rw [pow_succ]
      field_simp [hK.ne']

theorem dyadic_moment (k : ℕ) :
    moment (2^k) ≤ 2*(k:ℝ)*Real.log 4 := by
  induction k with
  | zero => simp [moment,Nat.primesLE_one]
  | succ k ih =>
    have inc : Nat.primesLE (2^k) ⊆ Nat.primesLE (2^(k+1)) :=
      Nat.primesLE_mono (by rw [pow_succ]; omega)
    have add :
        (∑ p ∈ Nat.primesLE (2^(k+1)) \ Nat.primesLE (2^k),
          Real.log (p:ℝ)/(p:ℝ)) + moment (2^k) =
          moment (2^(k+1)) := by
      unfold moment
      exact Finset.sum_sdiff inc
    rw [Nat.cast_succ]
    linarith only [ih,shell k,add]

theorem prime_moment_le (n : ℕ) (hn : 2 ≤ n) :
    moment n ≤ 8*Real.log (n:ℝ) := by
  let k := Nat.log 2 n
  have hhi : n ≤ 2^(k+1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hlo : 2^k ≤ n := Nat.pow_log_le_self _ (by omega)
  have h1 : 0 < (2:ℝ)^k := by positivity
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 0 < (n:ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hlog := (Real.log_le_log_iff h1 h2).mpr (by exact_mod_cast hlo)
  rw [Real.log_pow] at hlog
  have hlog2 := (Real.log_le_log_iff (by norm_num : (0:ℝ)<2) h2).mpr hnR
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hb := (monotone_moment hhi).trans (dyadic_moment (k+1))
  push_cast at hb
  rw [hlog4] at hb
  linarith only [hb,hlog,hlog2]

/-- This is uniform over every subset of the actual primes up to y. In
particular it applies after excluding the fixed wheel and one extra prime. -/
theorem weighted_moment (S : Finset ℕ) (g : ℕ → ℝ) (y : ℕ) (hy : 2≤y)
    (hS : S ⊆ Nat.primesLE y) (A : ℝ) (hA : 0≤A)
    (hg : ∀ p ∈ S, g p ≤ A/(p:ℝ)) :
    (∑ p ∈ S, g p*Real.log (p:ℝ)) ≤ (8*A)*Real.log (y:ℝ) := by
  calc
    _ ≤ ∑ p ∈ S, (A/(p:ℝ))*Real.log (p:ℝ) := by
      exact Finset.sum_le_sum (fun p hp =>
        mul_le_mul_of_nonneg_right (hg p hp)
          (prime_log_nonneg (Nat.mem_primesLE.mp (hS hp)).2))
    _ = A * ∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ A * moment y := by
      apply mul_le_mul_of_nonneg_left _ hA
      unfold moment
      exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
        div_nonneg (prime_log_nonneg (Nat.mem_primesLE.mp hp).2) (by positivity))
    _ ≤ A*(8*Real.log (y:ℝ)) := mul_le_mul_of_nonneg_left (prime_moment_le y hy) hA
    _ = (8*A)*Real.log (y:ℝ) := by ring

end LinearA4PrimeLogMoment318
