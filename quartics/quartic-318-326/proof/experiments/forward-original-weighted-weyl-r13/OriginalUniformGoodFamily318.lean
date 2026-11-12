module
public import OriginalUniformGoodTail318
public section
noncomputable section
namespace OriginalUniformGoodFamily318
open scoped BigOperators
open OriginalGoodLatticeSieveUnion318 OriginalGoodAllPrimeFamily318
open OriginalNormPointAllPrime318 OriginalUniformGoodTail318 OriginalUniformGoodHeight318
set_option maxHeartbeats 7500000

local instance goodFintype (κ t : ℤ) (T : ℝ) : Fintype (GoodParameters κ t T) := by
  classical
  letI : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      NeZero (LiteralSliceModulus318.prime κ t k) :=
    fun k => ⟨(LiteralSliceModulus318.prime_is_prime κ t k).ne_zero⟩
  infer_instance

@[expose] def parameterCount (κ t : ℤ) : ℕ :=
  ∏ k : LiteralSliceModulus318.PrimeIndex κ t, (LiteralSliceModulus318.prime κ t k+1)
@[expose] def familyWeight (κ t : ℤ) : ℝ :=
  (parameterCount κ t:ℝ)/(LiteralSliceModulus318.modulus κ t:ℝ)^2

lemma good_parameter_count (κ t : ℤ) (T : ℝ) : Nat.card (GoodParameters κ t T)≤parameterCount κ t := by
  classical
  letI : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      NeZero (LiteralSliceModulus318.prime κ t k) :=
    fun k => ⟨(LiteralSliceModulus318.prime_is_prime κ t k).ne_zero⟩
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : GoodParameters κ t T → ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      Option (ZMod (LiteralSliceModulus318.prime κ t k))) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_pi,Fintype.card_option,ZMod.card,parameterCount] using hh

lemma uniform_nonneg (κ t : ℤ) (R T : ℝ) (hR : 0≤R) (hT : 0≤T) (Y : ℕ) (hY : 3≤Y) :
    0≤uniformBudget κ t R T Y := by
  have hl := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hg := Real.log_nonneg (globalHeight_one κ t R)
  dsimp [uniformBudget]
  positivity

/-- The explicit same-frame budget sum is now eliminated using ORIGINAL
index normalization and the SAME good predicate. There is no assumed
per-lattice bound or asymptotic mass in this consumer. -/
theorem original_good_uniform_indexed (B : ℕ) (side : Bool) (κ t : ℤ) (hκ : κ≠0)
    (R T : ℝ) (hR : 0≤R) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (GoodPoints B side κ t R T Y):ℝ)*Real.log (Y:ℝ)*
      (LiteralSliceModulus318.modulus κ t:ℝ)^2≤
        (Nat.card (GoodParameters κ t T):ℝ)*uniformBudget κ t R T Y := by
  classical
  have hh := actual_good_all_prime_tail B side κ t hκ R T hR Y hY
  have hc := mul_le_mul_of_nonneg_right hh (sq_nonneg (LiteralSliceModulus318.modulus κ t:ℝ))
  rw [Finset.sum_mul] at hc
  have hs := Finset.sum_le_sum (fun s (_ : s∈Finset.univ) =>
    good_point_budget κ t s.1 R T hTR Y hY s.2)
  exact hc.trans (by simpa [Nat.card_eq_fintype_card] using hs)

/-- Actual original good-family ALL-prime tail with one explicit radical
weight: prod(p+1)/M². Summing this ORIGINAL label weight is the next
Rankin/Euler-product task, not silently replaced by a uniform constant. -/
theorem original_good_uniform_tail (B : ℕ) (side : Bool) (κ t : ℤ) (hκ : κ≠0)
    (R T : ℝ) (hR : 0≤R) (hT : 0≤T) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (GoodPoints B side κ t R T Y):ℝ)*Real.log (Y:ℝ)≤
      familyWeight κ t*uniformBudget κ t R T Y := by
  have hh := original_good_uniform_indexed B side κ t hκ R T hR hTR Y hY
  have hc : (Nat.card (GoodParameters κ t T):ℝ)≤(parameterCount κ t:ℝ) := by
    exact_mod_cast good_parameter_count κ t T
  have hu := uniform_nonneg κ t R T hR hT Y hY
  have hb := hh.trans (mul_le_mul_of_nonneg_right hc hu)
  have hM : (0:ℝ)<LiteralSliceModulus318.modulus κ t := by
    exact_mod_cast LiteralSliceModulus318.modulus_positive κ t
  have hm2 := sq_pos_of_pos hM
  calc
    _ ≤ ((parameterCount κ t:ℝ)*uniformBudget κ t R T Y)/
        (LiteralSliceModulus318.modulus κ t:ℝ)^2 := (le_div_iff₀ hm2).mpr hb
    _ = familyWeight κ t*uniformBudget κ t R T Y := by dsimp [familyWeight];ring

end OriginalUniformGoodFamily318
