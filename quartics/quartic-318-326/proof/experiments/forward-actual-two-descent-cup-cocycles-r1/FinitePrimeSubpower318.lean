module
public import OriginalBadSliceLogWeight318
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public section
noncomputable section
namespace FinitePrimeSubpower318
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- An explicit finite cutoff, depending only on the requested exponent
and multiplicity supportConstant, not on a slice or its prime support. -/
@[expose] def cutoff (A δ : ℝ) : ℕ := Nat.ceil (A ^ δ⁻¹)
@[expose] def supportConstant (A δ : ℝ) : ℝ := A ^ cutoff A δ

lemma constant_pos (A δ : ℝ) (hA : 1≤A) : 0<supportConstant A δ := by
  exact pow_pos (lt_of_lt_of_le zero_lt_one hA) _

lemma large_factor (A δ : ℝ) (hA : 1≤A) (hδ : 0<δ) (p : ℕ)
    (hp : cutoff A δ≤p) : A≤(p:ℝ)^δ := by
  have hAp : A^δ⁻¹≤(p:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (le_trans zero_le_one hA) (δ⁻¹)) hAp hδ.le
  simpa only [Real.rpow_inv_rpow (le_trans zero_le_one hA) hδ.ne'] using hh

lemma product_rpow (s : Finset ℕ) (δ : ℝ) :
    (∏ p∈s, (p:ℝ)^δ)=((∏ p∈s, p:ℕ):ℝ)^δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp,Finset.prod_insert hp,Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity),ih]

/-- A completely constructed subpower bound for the number of distinct
support primes. No divisor asymptotic or supplied omega bound is used.
The small primes occupy fewer than cutoff(A,δ) distinct natural slots. -/
theorem prime_support_bound (A δ : ℝ) (hA : 1≤A) (hδ : 0<δ)
    (s : Finset ℕ) (hs : ∀ p∈s, p.Prime) :
    A^s.card≤supportConstant A δ*((∏ p∈s, p:ℕ):ℝ)^δ := by
  classical
  let small := s.filter (fun p => p<cutoff A δ)
  let large := s.filter (fun p => ¬p<cutoff A δ)
  have hsmall : small.card≤cutoff A δ := by
    apply (Finset.card_le_card (show small⊆Finset.range (cutoff A δ) from ?_)).trans
      (by simp)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hpow : A^small.card≤supportConstant A δ := by
    exact pow_le_pow_right₀ hA hsmall
  have hlarge : (∏ p∈large, A)≤∏ p∈large, (p:ℝ)^δ := by
    apply Finset.prod_le_prod
    · intro p hp; exact le_trans zero_le_one hA
    · intro p hp
      exact large_factor A δ hA hδ p (by
        have h := (Finset.mem_filter.mp hp).2; omega)
  have hone : 1≤∏ p∈small, (p:ℝ)^δ := by
    apply Finset.one_le_prod
    intro p hp
    have hp1 : (1:ℝ)≤p := by
      exact_mod_cast (hs p (Finset.mem_filter.mp hp).1).one_lt.le
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hp1 hδ.le
  have hsplitA : A^s.card=A^small.card*(∏ p∈large, A) := by
    simpa only [Finset.prod_const] using
      (Finset.prod_filter_mul_prod_filter_not s (fun p => p<cutoff A δ) (fun _ => A)).symm
  have hsplitP : (∏ p∈small, (p:ℝ)^δ)*(∏ p∈large, (p:ℝ)^δ)=
      (∏ p∈s, (p:ℝ)^δ) :=
    Finset.prod_filter_mul_prod_filter_not s (fun p => p<cutoff A δ) _
  calc
    A^s.card = A^small.card*(∏ p∈large, A) := hsplitA
    _ ≤ supportConstant A δ*(∏ p∈large, (p:ℝ)^δ) :=
      mul_le_mul hpow hlarge (Finset.prod_nonneg (fun _ _ => le_trans zero_le_one hA))
        (constant_pos A δ hA).le
    _ ≤ supportConstant A δ*((∏ p∈small, (p:ℝ)^δ)*(∏ p∈large, (p:ℝ)^δ)) := by
      apply mul_le_mul_of_nonneg_left _ (constant_pos A δ hA).le
      exact le_mul_of_one_le_left (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg (by positivity) _)) hone
    _ = supportConstant A δ*((∏ p∈s, p:ℕ):ℝ)^δ := by rw [hsplitP,product_rpow]

/-- This consumes the actual retained primes and their actual product,
without changing the original coefficient or introducing a free modulus. -/
theorem actual_retained_bound (κ label : ℤ) (δ : ℝ) (hδ : 0<δ) :
    (4:ℝ)^(LiteralSliceModulus318.retained κ label).card≤
      supportConstant 4 δ*(LiteralSliceModulus318.modulus κ label:ℝ)^δ := by
  have h := prime_support_bound 4 δ (by norm_num) hδ
    (LiteralSliceModulus318.retained κ label)
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  simpa only [LiteralSliceModulus318.modulus,FixedSquarefreeCRT318.modulus,
    LiteralSliceModulus318.prime,LiteralSliceModulus318.PrimeIndex,Finset.prod_coe_sort] using h

end FinitePrimeSubpower318
