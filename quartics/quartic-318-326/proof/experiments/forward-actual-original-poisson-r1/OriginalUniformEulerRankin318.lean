module
public import OriginalFiniteLabelRankin318
public section
noncomputable section
namespace OriginalUniformEulerRankin318
open scoped BigOperators
open OriginalRetainedFamilyWeight318 OriginalRetainedDirichlet318 OriginalFiniteLabelRankin318
open OriginalUniformGoodFamily318
set_option maxHeartbeats 8500000

@[expose] def badPrimes (κ : ℤ) := (2*κ).natAbs.primeFactors
@[expose] def badProduct (κ : ℤ) (δ : ℝ) := ∏ p∈badPrimes κ, localFactor κ δ p
@[expose] def excessConstant (δ : ℝ) := 2/(1-ratio δ 2)
@[expose] def pseries (δ : ℝ) : ℝ := ∑' n : ℕ, (n:ℝ)^(-1-δ)
@[expose] def rankinConstant (κ : ℤ) (δ : ℝ) :=
  badProduct κ δ*Real.exp (excessConstant δ*pseries δ)

lemma mem_badPrimes (κ : ℤ) (hκ : κ≠0) (p : ℕ) (hp : p.Prime) :
    p∈badPrimes κ ↔ (p:ℤ)∣2*κ := by
  have hn : (2*κ).natAbs≠0 := Int.natAbs_ne_zero.mpr (mul_ne_zero (by norm_num) hκ)
  rw [badPrimes,Nat.mem_primeFactors_of_ne_zero hn]
  constructor
  · intro h
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h.2)
  · intro h
    exact ⟨hp,by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h⟩

lemma excessConstant_pos (δ : ℝ) (hδ : 0<δ) : 0<excessConstant δ := by
  have hh := ratio_lt_one δ hδ 2 Nat.prime_two
  exact div_pos (by norm_num) (sub_pos.mpr hh)

/-- A retained prime contributes a genuinely summable p^(-1-delta)
excess. The denominator bound is UNIFORM in p>=2 and proved from rpow
monotonicity, not from an assumed Euler-product convergence theorem. -/
lemma local_excess (κ : ℤ) (δ : ℝ) (hδ : 0<δ) (p : ℕ) (hp : p.Prime)
    (hbad : ¬(p:ℤ)∣2*κ) :
    localFactor κ δ p≤1+excessConstant δ*(p:ℝ)^(-1-δ) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have h2p : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hr0 := ratio_positive δ p hp
  have hr1 := ratio_lt_one δ hδ p hp
  have htwo := ratio_lt_one δ hδ 2 Nat.prime_two
  have hratio : ratio δ p≤ratio δ 2 :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2p (by linarith)
  have hw := retained_weight_bound κ p hp hbad
  have hnum := mul_le_mul_of_nonneg_right hw hr0.le
  have hden : 1-ratio δ 2≤1-ratio δ p := by linarith
  have hb : primeWeight κ p*ratio δ p/(1-ratio δ p)≤
      (2/(p:ℝ)*ratio δ p)/(1-ratio δ 2) :=
    (div_le_div_of_nonneg_right hnum (sub_pos.mpr hr1).le).trans
      (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr htwo) hden)
  have he : (2/(p:ℝ)*ratio δ p)/(1-ratio δ 2)=excessConstant δ*(p:ℝ)^(-1-δ) := by
    rw [show (-1:ℝ)-δ=(-1)+(-δ) by ring,Real.rpow_add hpR,Real.rpow_neg_one]
    dsimp [excessConstant,ratio]
    ring
  exact add_le_add_left (hb.trans_eq he) 1

lemma pseries_summable (δ : ℝ) (hδ : 0<δ) : Summable (fun n : ℕ => (n:ℝ)^(-1-δ)) :=
  Real.summable_nat_rpow.mpr (by linarith)
lemma pseries_nonneg (δ : ℝ) : 0≤pseries δ :=
  tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma badProduct_one (κ : ℤ) (δ : ℝ) (hδ : 0<δ) : 1≤badProduct κ δ := by
  apply Finset.one_le_prod
  intro p hp
  exact localFactor_one_le κ δ hδ p (Nat.prime_of_mem_primeFactors hp)

/-- The actual finite Euler products are bounded UNIFORMLY in the label
cutoff. Primes dividing2*kappa retain their exact FULL local series in
badProduct; all other prime factors are dominated by the convergent p-series. -/
theorem localProduct_bound (κ : ℤ) (hκ : κ≠0) (δ : ℝ) (hδ : 0<δ) (B : ℕ) :
    localProduct κ δ B≤rankinConstant κ δ := by
  classical
  let S := (Finset.range (B+1)).filter Nat.Prime
  let b : ℕ → ℝ := fun p => if p∈badPrimes κ then localFactor κ δ p else 1
  let a : ℕ → ℝ := fun p => excessConstant δ*(p:ℝ)^(-1-δ)
  have hC : 0≤excessConstant δ := (excessConstant_pos δ hδ).le
  have ha (p : ℕ) : 0≤a p := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hpoint (p : ℕ) (hp : p∈S) : localFactor κ δ p≤b p*Real.exp (a p) := by
    have hp' := (Finset.mem_filter.mp hp).2
    have hexp : 1≤Real.exp (a p) := by
      have hh := Real.add_one_le_exp (a p)
      linarith [ha p]
    by_cases hb : p∈badPrimes κ
    · simpa [b,hb] using mul_le_mul_of_nonneg_left hexp
        ((zero_le_one.trans (localFactor_one_le κ δ hδ p hp')))
    · have havoid : ¬(p:ℤ)∣2*κ := fun h => hb ((mem_badPrimes κ hκ p hp').mpr h)
      have hh := local_excess κ δ hδ p hp' havoid
      have he := Real.add_one_le_exp (a p)
      simpa [b,hb,a] using hh.trans (by simpa only [add_comm] using he)
  have hprod := Finset.prod_le_prod
    (fun p hp => zero_le_one.trans (localFactor_one_le κ δ hδ p (Finset.mem_filter.mp hp).2)) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hbprod : (∏ p∈S,b p)≤badProduct κ δ := by
    have he : (∏ p∈S,b p)=∏ p∈S.filter (fun p => p∈badPrimes κ),localFactor κ δ p := by
      simp only [Finset.prod_filter,b]
    rw [he]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
      (fun p hp => (Finset.mem_filter.mp hp).2)
    · intro p hp
      exact zero_le_one.trans (localFactor_one_le κ δ hδ p
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
    · intro p hp _
      exact localFactor_one_le κ δ hδ p (Nat.prime_of_mem_primeFactors hp)
  have hsum : (∑ p∈S, (p:ℝ)^(-1-δ))≤pseries δ :=
    sum_le_hasSum S (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (pseries_summable δ hδ).hasSum
  have hexpprod : (∏ p∈S,Real.exp (a p))≤Real.exp (excessConstant δ*pseries δ) := by
    rw [←Real.exp_sum]
    apply Real.exp_le_exp.mpr
    change (∑ p∈S, excessConstant δ*(p:ℝ)^(-1-δ))≤_
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum hC
  change (∏ p∈S,localFactor κ δ p)≤_
  exact hprod.trans (mul_le_mul hbprod hexpprod
    (Finset.prod_nonneg (fun p _ => (Real.exp_pos _).le))
    (zero_le_one.trans (badProduct_one κ δ hδ)))

lemma rankinConstant_pos (κ : ℤ) (δ : ℝ) (hδ : 0<δ) : 0<rankinConstant κ δ :=
  mul_pos (zero_lt_one.trans_le (badProduct_one κ δ hδ)) (Real.exp_pos _)

/-- The ORIGINAL positive-label family weight has a proved subpower
summatory bound for EVERY delta>0. The coefficient depends on actualkappa
anddelta, never on label cutoffB or an unproved summability hypothesis. -/
theorem actual_positive_label_sum (κ : ℤ) (hκ : κ≠0) (δ : ℝ) (hδ : 0<δ) (B : ℕ) :
    (∑ n∈Finset.Icc 1 B, familyWeight κ (n:ℤ))≤rankinConstant κ δ*(B:ℝ)^δ := by
  have hh := actual_finite_rankin κ δ hδ B
  have hb := mul_le_mul_of_nonneg_left (localProduct_bound κ hκ δ hδ B)
    (Real.rpow_nonneg (Nat.cast_nonneg B) δ)
  simpa only [mul_comm] using hh.trans hb

end OriginalUniformEulerRankin318
