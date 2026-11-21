module
public import Mathlib
public section
noncomputable section
namespace ActualSmallCoefficientPrimeBudget318

open scoped BigOperators

/-- Distinct bad primes all divide the very same nonzero integer
coefficient. The sign of that integer is irrelevant. -/
theorem bad_product_dvd_abs (S : Finset ℕ) (c : ℤ)
    (h : ∀ p∈S,p.Prime ∧ (p:ℤ)∣c) : (∏ p∈S,p)∣c.natAbs := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have h₀ := h p (Finset.mem_insert_self _ _)
    have hS : ∀ q∈S,q.Prime ∧ (q:ℤ)∣c :=
      fun q hq => h q (Finset.mem_insert_of_mem hq)
    have hCop : (∏ q∈S,q).Coprime p := by
      apply Nat.Coprime.prod_left
      intro q hq
      exact (Nat.coprime_primes (hS q hq).1 h₀.1).mpr
        (fun he => hp (he ▸ hq))
    have hd : p∣c.natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h₀.2)
    rw [Finset.prod_insert hp]
    exact hCop.symm.mul_dvd_of_dvd_of_dvd hd (ih hS)

theorem bad_power_le_abs (S : Finset ℕ) {y : ℕ} {c : ℤ} (hc : c≠0)
    (h : ∀ p∈S,p.Prime ∧ y≤p ∧ (p:ℤ)∣c) : y^S.card≤c.natAbs := by
  have hp : y^S.card≤∏ p∈S,p := by
    simpa only [Finset.prod_const] using
      (Finset.prod_le_prod (s:=S) (f:=fun _ => y) (g:=fun p => p)
        (fun p hp => (h p hp).2.1))
  have hc₀ : 0<c.natAbs := Nat.pos_of_ne_zero (fun hz => hc (Int.natAbs_eq_zero.mp hz))
  exact hp.trans (Nat.le_of_dvd hc₀ (bad_product_dvd_abs S c
    (fun p hp => ⟨(h p hp).1,(h p hp).2.2⟩)))

/-- No cutoff asymptotic is asserted: this is the finite inequality
that, after the true wheel estimate, gives O(1/log y). -/
theorem bad_reciprocal_le (S : Finset ℕ) {y : ℕ} {c : ℤ} (hy : 1<y) (hc : c≠0)
    (h : ∀ p∈S,p.Prime ∧ y≤p ∧ (p:ℤ)∣c) :
    (∑ p∈S,1/(p:ℝ))≤Real.log (c.natAbs:ℝ)/((y:ℝ)*Real.log (y:ℝ)) := by
  have hy₁ : (1:ℝ)<(y:ℝ) := by exact_mod_cast hy
  have hy₀ : (0:ℝ)<(y:ℝ) := zero_lt_one.trans hy₁
  have hlog := Real.log_pos hy₁
  have hp : (y:ℝ)^S.card≤(c.natAbs:ℝ) := by
    exact_mod_cast bad_power_le_abs S hc h
  have hl := Real.log_le_log (pow_pos hy₀ _) hp
  rw [Real.log_pow] at hl
  calc
    _ ≤ ∑ _p∈S,1/(y:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpy : (y:ℝ)≤(p:ℝ) := by exact_mod_cast (h p hp).2.1
      exact one_div_le_one_div_of_le hy₀ hpy
    _ = (S.card:ℝ)/(y:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul]
    _ ≤ _ := by
      apply (le_div_iff₀ (mul_pos hy₀ hlog)).2
      calc
        (S.card:ℝ)/(y:ℝ)*((y:ℝ)*Real.log (y:ℝ)) =
            (S.card:ℝ)*Real.log (y:ℝ) := by field_simp [hy₀.ne'] <;> ring
        _ ≤ _ := hl

end ActualSmallCoefficientPrimeBudget318
