module
public import ActualLinearQLiteralFoldCalibration318
public import Mathlib
public section
noncomputable section
namespace ActualLinearQFoldedDenominator318

open scoped BigOperators
open ActualLinearQArithmeticCalibration318
open ActualLinearQOrderOneCalibration318 ActualLinearQLiteralFoldCalibration318

/-- Exact square factor in the linear-q contact identity. The third
power of q here is essential; the prefactor q consumes its odd power. -/
@[expose] def rootFactor (τ c u A q : ℚ) : ℚ :=
  τ/(A^5*q^3*(delta c u A q)^3)

/-- In reduced lowest terms, outside the support of a positive
integral prefactor all rational valuations are even; on its
support nonnegativity of the root-factor valuation suffices. -/
theorem positive_integer_square_den (N : ℕ) (s : ℚ) (hN : N ≠ 0) (hs : s ≠ 0)
    (hSupport : ∀ p : ℕ, p.Prime → p ∣ N → 0 ≤ padicValRat p s) :
    IsSquare (((N:ℚ)*s^2).den) := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let z : ℚ := (N:ℚ)*s^2
  have hv : padicValRat p z=(padicValNat p N:ℤ)+2*padicValRat p s := by
    dsimp only [z]
    rw [padicValRat.mul (by exact_mod_cast hN) (pow_ne_zero _ hs),
      padicValRat.of_nat,padicValRat.pow] <;> norm_num
  have hZ : 0 ≤ padicValRat p z ∨ Even (padicValRat p z) := by
    by_cases hD : p ∣ N
    · left
      rw [hv]
      exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (hSupport p hp hD))
    · right
      rw [hv,padicValNat.eq_zero_of_not_dvd hD,Nat.cast_zero,zero_add]
      exact ⟨padicValRat p s,by ring⟩
  have hden : Even (padicValNat p z.den) := by
    rcases hZ with h|h
    · rcases Rat.num_or_den_zero_padicVal z hp with hn|hd
      · have hz : padicValNat p z.den=0 := by
          simp only [padicValRat_def,hn,Nat.cast_zero,zero_sub] at h
          omega
        simp [hz]
      · simp [hd]
    · exact (Rat.num_den_even_padicVal_of_even_padicVal hp h).2
  simpa only [Nat.factorization_def _ hp,z] using hden

/-- The only possible positive-integral support is the extra
denominator prime and these exact five contact factors. No condition
on primes outside these six places, or distinctness assumption, is used. -/
theorem six_place_den (τ c u A : ℚ) (q : ℕ) (hq : q.Prime) (n : Fin 5 → ℕ)
    (hn : ∀ i, (n i).Prime)
    (hProduct : factorProduct c u A q = ((∏ i : Fin 5, n i):ℚ))
    (hτ : τ ≠ 0) (hc : c ≠ 0) (hA : A ≠ 0) (hDelta : delta c u A q ≠ 0)
    (hqUnit : 0 ≤ padicValRat q (rootFactor τ c u A q))
    (hContact : ∀ i, 0 ≤ padicValRat (n i) (rootFactor τ c u A q)) :
    IsSquare (pole τ c u A q).den := by
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let N : ℕ := q * ∏ i : Fin 5, n i
  have hN : N ≠ 0 := mul_ne_zero hq.ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hn i).ne_zero))
  have hRoot : rootFactor τ c u A q ≠ 0 := div_ne_zero hτ
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hq0))
      (pow_ne_zero _ hDelta))
  have hSupp (p : ℕ) (hp : p.Prime) (h : p ∣ N) :
      0 ≤ padicValRat p (rootFactor τ c u A q) := by
    rcases hp.dvd_mul.mp (show p ∣ q * ∏ i : Fin 5, n i from h) with hQ|hN'
    · rw [(Nat.prime_dvd_prime_iff_eq hp hq).mp hQ]
      exact hqUnit
    · obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hN'
      rw [(Nat.prime_dvd_prime_iff_eq hp (hn i)).mp hi]
      exact hContact i
  have H := positive_integer_square_den N (rootFactor τ c u A q) hN hRoot hSupp
  have eq : pole τ c u A q=(N:ℚ)*(rootFactor τ c u A q)^2 := by
    rw [pole_squareclass τ c u A q hc hA hq0 hDelta,hProduct] <;>
      simp only [N,Nat.cast_mul,rootFactor]
  rw [eq]
  exact H

/-- At the actual folded value the q-place root-factor unit is derived
from the verified order-one fold, not supplied a second time. Only the
five explicit CONTACT root-factor valuation inequalities remain. -/
theorem folded_denominator (w : ℕ → ℚ) (c u A : ℚ) (q : ℕ) [Fact q.Prime]
    (hqLarge : 2399 < q) (n : Fin 5 → ℕ) (hn : ∀ i, (n i).Prime)
    (hProduct : factorProduct c u A q = ((∏ i : Fin 5, n i):ℚ))
    (hc : c ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0)
    (hc0 : padicValRat q c = 0) (hu0 : padicValRat q u = 0) (hA0 : padicValRat q A = 0)
    (hCoeff : ∀ e ∈ coefficients w, 0 ≤ val q e.2.1 ∧ 0 ≤ val q e.2.2)
    (hContact : ∀ i, 0 ≤ padicValRat (n i) (rootFactor (trace (fold w c u A q)) c u A q)) :
    trace (fold w c u A q) ≠ 0 ∧ delta c u A q ≠ 0 ∧
      padicValRat q (pole (trace (fold w c u A q)) c u A q)=1 ∧
      IsSquare (pole (trace (fold w c u A q)) c u A q).den := by
  have hqp : q.Prime := Fact.out
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  obtain ⟨_,_,hD,hDv⟩ := contact_delta q hqLarge c u A hc hu hA hc0 hu0 hA0
  obtain ⟨hτ,hτv,hPole⟩ := order_one_gate q hqLarge w c u A hc hu hA hc0 hu0 hA0 hCoeff
  have hQv : padicValRat q (rootFactor (trace (fold w c u A q)) c u A q)=0 := by
    rw [rootFactor,padicValRat.div hτ
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hq0))
        (pow_ne_zero _ hD)),
      padicValRat.mul (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hq0)) (pow_ne_zero _ hD),
      padicValRat.mul (pow_ne_zero _ hA) (pow_ne_zero _ hq0),
      padicValRat.pow,padicValRat.pow,padicValRat.pow,hτv,hA0,padicValRat.self hqp.one_lt,hDv] <;> norm_num
  exact ⟨hτ,hD,hPole,six_place_den _ c u A q hqp n hn hProduct hτ hc hA hD hQv.ge hContact⟩

/-- All three actual detector folds at one shared w,u,A,q. Contact
forms and scales remain row-specific; no h or numerator is rechosen.
The separate scalar (fourth) pole uses the existing scalar path. -/
theorem three_folded_denominators (w : ℕ → ℚ) (u A : ℚ) (q : ℕ) [Fact q.Prime]
    (hqLarge : 2399 < q) (c : Fin 3 → ℚ) (n : Fin 3 → Fin 5 → ℕ)
    (hn : ∀ j i, (n j i).Prime)
    (hProduct : ∀ j, factorProduct (c j) u A q = ((∏ i : Fin 5, n j i):ℚ))
    (hc : ∀ j, c j ≠ 0) (hu : u ≠ 0) (hA : A ≠ 0)
    (hc0 : ∀ j, padicValRat q (c j) = 0) (hu0 : padicValRat q u = 0)
    (hA0 : padicValRat q A = 0)
    (hCoeff : ∀ e ∈ coefficients w, 0 ≤ val q e.2.1 ∧ 0 ≤ val q e.2.2)
    (hContact : ∀ j i,
      0 ≤ padicValRat (n j i) (rootFactor (trace (fold w (c j) u A q)) (c j) u A q)) :
    ∀ j, padicValRat q (pole (trace (fold w (c j) u A q)) (c j) u A q)=1 ∧
      IsSquare (pole (trace (fold w (c j) u A q)) (c j) u A q).den := by
  intro j
  exact (folded_denominator w (c j) u A q hqLarge (n j) (hn j) (hProduct j)
    (hc j) hu hA (hc0 j) hu0 hA0 hCoeff (hContact j)).2.2

end ActualLinearQFoldedDenominator318
