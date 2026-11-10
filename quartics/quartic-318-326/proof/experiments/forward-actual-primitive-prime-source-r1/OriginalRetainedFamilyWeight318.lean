module
public import OriginalUniformGoodFamily318
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.PSeries
public section
noncomputable section
namespace OriginalRetainedFamilyWeight318
open scoped BigOperators
open OriginalUniformGoodFamily318
set_option maxHeartbeats 7000000

/-- Primes dividing ORIGINAL2*kappa are unpenalized, including arbitrary
powers in the original label. Every other prime has exact(p+1)/p² weight. -/
@[expose] def primeWeight (κ : ℤ) (p : ℕ) : ℝ :=
  if (p:ℤ)∣2*κ then 1 else ((p:ℝ)+1)/(p:ℝ)^2
@[expose] def weight (κ : ℤ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (primeWeight κ)

lemma familyWeight_product (κ t : ℤ) : familyWeight κ t=
    ∏ p∈LiteralSliceModulus318.retained κ t, ((p:ℝ)+1)/(p:ℝ)^2 := by
  unfold familyWeight parameterCount LiteralSliceModulus318.modulus FixedSquarefreeCRT318.modulus
  simp only [LiteralSliceModulus318.prime]
  push_cast
  rw [←Finset.prod_pow,←Finset.prod_div_distrib]
  simp only [LiteralSliceModulus318.PrimeIndex,Finset.prod_coe_sort]

/-- The Euler weight is identified at the FINAL point-count coefficient,
including the integer-index denominator. This is not a replacement form. -/
lemma actual_weight (κ : ℤ) (n : ℕ) (hn : n≠0) : weight κ n=familyWeight κ (n:ℤ) := by
  rw [weight,ArithmeticFunction.prodPrimeFactors_apply hn,familyWeight_product]
  simp only [LiteralSliceModulus318.retained,Int.natAbs_natCast,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : (p:ℤ)∣2*κ <;> simp [primeWeight,h]

/-- Signed original labels retain exactly the same weight. The only
zero convention is on the arithmetic-function extension at n=0, which is
never substituted for a nonzero original slice. -/
lemma signed_weight (κ t : ℤ) (ht : t≠0) : weight κ t.natAbs=familyWeight κ t := by
  rw [actual_weight κ t.natAbs (Int.natAbs_ne_zero.mpr ht),familyWeight_product,familyWeight_product]
  simp only [LiteralSliceModulus318.retained,Int.natAbs_natCast]

lemma weight_zero (κ : ℤ) : weight κ 0=0 := (weight κ).map_zero
lemma weight_one (κ : ℤ) : weight κ 1=1 := by simp [weight,ArithmeticFunction.prodPrimeFactors_apply]
lemma weight_mul (κ : ℤ) {m n : ℕ} (h : m.Coprime n) : weight κ (m*n)=weight κ m*weight κ n :=
  (ArithmeticFunction.IsMultiplicative.prodPrimeFactors (primeWeight κ)).2 h

lemma weight_prime_power (κ : ℤ) (p e : ℕ) (hp : p.Prime) : weight κ (p^(e+1))=primeWeight κ p := by
  rw [weight,ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_pow_succ]
  simp [hp.primeFactors]

lemma primeWeight_nonneg (κ : ℤ) (p : ℕ) : 0≤primeWeight κ p := by
  unfold primeWeight
  split_ifs <;> positivity
lemma weight_nonneg (κ : ℤ) (n : ℕ) : 0≤weight κ n := by
  by_cases hn : n=0
  · simpa only [hn,weight_zero] using (le_refl (0:ℝ))
  · rw [weight,ArithmeticFunction.prodPrimeFactors_apply hn]
    exact Finset.prod_nonneg (fun p _ => primeWeight_nonneg κ p)

lemma primeWeight_pos (κ : ℤ) (p : ℕ) (hp : p.Prime) : 0<primeWeight κ p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  unfold primeWeight
  split_ifs <;> positivity

lemma primeWeight_le_one (κ : ℤ) (p : ℕ) (hp : p.Prime) : primeWeight κ p≤1 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs
  · exact le_rfl
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<(p:ℝ)^2)).mpr
    nlinarith

lemma retained_weight_bound (κ : ℤ) (p : ℕ) (hp : p.Prime) (hbad : ¬(p:ℤ)∣2*κ) :
    primeWeight κ p≤2/(p:ℝ) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  simp only [primeWeight,if_neg hbad]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpR) hpR).mpr
  nlinarith

end OriginalRetainedFamilyWeight318
