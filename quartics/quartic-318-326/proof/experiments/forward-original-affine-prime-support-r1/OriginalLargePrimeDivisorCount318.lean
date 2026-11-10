module
public import OriginalWholeBasisEliminants318
public section
noncomputable section
namespace OriginalLargePrimeDivisorCount318
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- Distinct actual prime divisors of a nonzero INTEGER have product
bounded by its absolute value, even when the integer is negative. -/
theorem prime_product_le (n : ℤ) (hn : n≠0) (S : Finset ℕ)
    (hp : ∀ p∈S, p.Prime) (hd : ∀ p∈S, (p:ℤ)∣n) :
    (∏ p∈S, p:ℕ)≤n.natAbs := by
  classical
  let q : ↥S → ℕ := Subtype.val
  have hq : ∀ i, (q i).Prime := fun i => hp i.1 i.2
  have hinj : Function.Injective q := Subtype.val_injective
  have hdiv := (SquarefreeTernaryLatticeCover318.product_divisor_iff q hq hinj n).mpr
    (fun i => hd i.1 i.2)
  have hnat := Int.natAbs_dvd_natAbs.mpr hdiv
  have he : (FixedSquarefreeCRT318.modulus q:ℤ).natAbs=∏ p∈S,p := by
    simp only [Int.natAbs_natCast,FixedSquarefreeCRT318.modulus,q,Finset.prod_coe_sort]
  rw [he] at hnat
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hnat

/-- A finite large-prime count obtained from actual distinct divisors,
not an assumed prime-density or sieve estimate. The logarithmic threshold
is explicit and greater than one. -/
theorem actual_divisor_log_count (n : ℤ) (hn : n≠0) (H : ℝ) (hH : 1<H)
    (S : Finset ℕ) (hp : ∀ p∈S, p.Prime) (hd : ∀ p∈S, (p:ℤ)∣n)
    (hlarge : ∀ p∈S, H≤(p:ℝ)) :
    (S.card:ℝ)*Real.log H≤Real.log (n.natAbs:ℝ) := by
  have hprod : H^S.card≤((∏ p∈S,p:ℕ):ℝ) := by
    rw [←Finset.prod_const]
    push_cast
    exact Finset.prod_le_prod (fun _ _ => (zero_lt_one.trans hH).le) hlarge
  have hnR : (0:ℝ)<n.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hn
  have hbound : H^S.card≤(n.natAbs:ℝ) := hprod.trans (by exact_mod_cast prime_product_le n hn S hp hd)
  have hh := Real.log_le_log (pow_pos (zero_lt_one.trans hH) _) hbound
  simpa only [Real.log_pow] using hh

/-- The actual finite set of large divisors of a concrete nonzero
eliminant. Zero values are excluded explicitly and handled as a separate
geometric locus rather than fed into this finite-prime argument. -/
@[expose] def largeDivisors (n : ℤ) (H : ℕ) : Finset ℕ :=
  n.natAbs.primeFactors.filter (fun p => H<p)

lemma mem_largeDivisors (n : ℤ) (hn : n≠0) (H p : ℕ) :
    p∈largeDivisors n H ↔ p.Prime ∧ (p:ℤ)∣n ∧ H<p := by
  have hd : p∣n.natAbs ↔ (p:ℤ)∣n := by
    constructor
    · intro h
      exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
    · intro h
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h)
  simp only [largeDivisors,Finset.mem_filter,
    Nat.mem_primeFactors_of_ne_zero (Int.natAbs_ne_zero.mpr hn),hd,and_assoc]

/-- Every actual large divisor of a nonzero fiber is counted, with a
concrete height budget at the consumption site. -/
theorem actual_large_divisor_height (n : ℤ) (hn : n≠0) (Y : ℕ) (hY : 1<Y)
    (L : ℝ) (hL : |(n:ℝ)|≤L) :
    ((largeDivisors n Y).card:ℝ)*Real.log (Y:ℝ)≤Real.log L := by
  have hh := actual_divisor_log_count n hn (Y:ℝ) (by exact_mod_cast hY)
    (largeDivisors n Y)
    (fun p hp => ((mem_largeDivisors n hn Y p).mp hp).1)
    (fun p hp => ((mem_largeDivisors n hn Y p).mp hp).2.1)
    (fun p hp => by exact_mod_cast (((mem_largeDivisors n hn Y p).mp hp).2.2).le)
  have hnR : (0:ℝ)<n.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hn
  have habs : (n.natAbs:ℝ)=|(n:ℝ)| := by exact_mod_cast Int.natCast_natAbs n
  exact hh.trans (Real.log_le_log hnR (by simpa only [habs] using hL))

/-- Constructed count for the ACTUAL quadratic eliminant used by the
original affine obstruction theorem, with its exact coefficient budget. -/
theorem actual_eliminant_prime_count (a b c d e f : ℤ)
    (hne : OriginalQuadraticEliminant318.eliminant a b c d e f≠0)
    (H K : ℝ) (hH : 0≤H) (hK : 0≤K)
    (ha : |(a:ℝ)|≤H) (hb : |(b:ℝ)|≤H) (hc : |(c:ℝ)|≤H)
    (hd : |(d:ℝ)|≤K) (he : |(e:ℝ)|≤K) (hf : |(f:ℝ)|≤K)
    (Y : ℕ) (hY : 1<Y) :
    ((largeDivisors (OriginalQuadraticEliminant318.eliminant a b c d e f) Y).card:ℝ)*
      Real.log (Y:ℝ)≤Real.log (8*H^2*K^2) :=
  actual_large_divisor_height _ hne Y hY _
    (OriginalQuadraticEliminant318.eliminant_abs_bound a b c d e f H K hH hK ha hb hc hd he hf)

end OriginalLargePrimeDivisorCount318
