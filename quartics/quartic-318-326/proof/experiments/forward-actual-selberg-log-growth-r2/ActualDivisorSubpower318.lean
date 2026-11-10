module
public import ActualIntegerFactorPairs318
public section
noncomputable section
namespace ActualDivisorSubpower318
open scoped BigOperators
open FinitePrimeSubpower318
set_option maxHeartbeats 12000000

/-- Elementary exponent multiplicity bound, including exponent zero.
It replaces an assumed divisor asymptotic by a constructed local factor. -/
lemma multiplicity_bound (q : ℝ) (hq : 1<q) (e : ℕ) :
    (e+1:ℝ)≤(q/(q-1))*q^e := by
  have hq0 : 0≤q := (zero_lt_one.trans hq).le
  have hh : ∀ e : ℕ, (e+1:ℝ)*(q-1)≤q^(e+1) := by
    intro e
    induction e with
    | zero => norm_num;linarith
    | succ e ih =>
      have hp : 1≤q^(e+1) := one_le_pow₀ hq.le
      have hm := mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hp)
      push_cast
      rw [pow_succ]
      nlinarith only [ih,hm]
  calc
    _ ≤ q^(e+1)/(q-1) := (le_div_iff₀ (sub_pos.mpr hq)).mpr (hh e)
    _ = _ := by
      rw [pow_succ]
      field_simp [ne_of_gt (sub_pos.mpr hq)]
      <;> ring

@[expose] def localConstant (η : ℝ) : ℝ := (2:ℝ)^η/((2:ℝ)^η-1)
lemma localConstant_one (η : ℝ) (hη : 0<η) : 1≤localConstant η := by
  have hq : 1<(2:ℝ)^η := Real.one_lt_rpow (by norm_num) hη
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  linarith

lemma prime_power_multiplicity (η : ℝ) (hη : 0<η) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    (e+1:ℝ)≤localConstant η*((p^e:ℕ):ℝ)^η := by
  have hq : 1<(2:ℝ)^η := Real.one_lt_rpow (by norm_num) hη
  have hb := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤2)
    (show (2:ℝ)≤p by exact_mod_cast hp.two_le) hη.le
  have he := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) η) hb e
  have hh := mul_le_mul_of_nonneg_left he ((zero_le_one.trans (localConstant_one η hη)))
  have hp0 : (0:ℝ)≤p := by positivity
  have hpow : ((p:ℝ)^η)^e=((p^e:ℕ):ℝ)^η := by
    rw [Nat.cast_pow,←Real.rpow_mul_natCast hp0,mul_comm η (e:ℝ),Real.rpow_natCast_mul hp0]
  exact (multiplicity_bound ((2:ℝ)^η) hq e).trans (by simpa only [hpow,localConstant] using hh)

@[expose] def divisorConstant (δ : ℝ) : ℝ :=
  supportConstant (localConstant (δ/2)) (δ/2)
lemma divisorConstant_pos (δ : ℝ) (hδ : 0<δ) : 0<divisorConstant δ :=
  constant_pos _ _ (localConstant_one _ (by linarith))

/-- Genuine divisor-count subpower estimate. Exponent multiplicities are
handled locally, while the distinct-prime support factor is bounded by
the already CONSTRUCTED supportConstant. No divisor asymptotic is imported
as a hypothesis. The exponent split delta/2+delta/2 is explicit. -/
theorem actual_divisor_subpower (δ : ℝ) (hδ : 0<δ) (n : ℕ) (hn : n≠0) :
    (n.divisors.card:ℝ)≤divisorConstant δ*(n:ℝ)^δ := by
  classical
  let η := δ/2
  have hη : 0<η := by dsimp [η];linarith
  have hprod : (∏ p∈n.primeFactors,p^n.factorization p)=n := by
    simpa only [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn
  have hfactor : (∏ p∈n.primeFactors,((p^n.factorization p:ℕ):ℝ)^η)=(n:ℝ)^η := by
    -- Finite indexed product, retaining every actual exponent.
    have he : ∀ S : Finset ℕ,
        (∏ p∈S,((p^n.factorization p:ℕ):ℝ)^η)=
          ((∏ p∈S,p^n.factorization p:ℕ):ℝ)^η := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert p S hp ih =>
        rw [Finset.prod_insert hp,Finset.prod_insert hp,Nat.cast_mul,
          Real.mul_rpow (by positivity) (by positivity),ih]
    simpa only [hprod] using he n.primeFactors
  have hlocal : (n.divisors.card:ℝ)≤
      (localConstant η)^n.primeFactors.card*(n:ℝ)^η := by
    rw [Nat.card_divisors hn,Nat.cast_prod]
    have hh : (∏ p∈n.primeFactors,((n.factorization p:ℝ)+1))≤
        ∏ p∈n.primeFactors,localConstant η*((p^n.factorization p:ℕ):ℝ)^η :=
      Finset.prod_le_prod (fun p _ => by positivity)
        (fun p hp => prime_power_multiplicity η hη p (Nat.prime_of_mem_primeFactors hp) (n.factorization p))
    simpa only [Nat.cast_add,Nat.cast_one,Finset.prod_mul_distrib,Finset.prod_const,hfactor] using hh
  have hsupport := prime_support_bound (localConstant η) η (localConstant_one η hη) hη
    n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hrad : (∏ p∈n.primeFactors,p:ℕ)≤n := by
    have hh := OriginalLargePrimeDivisorCount318.prime_product_le (n:ℤ)
      (by exact_mod_cast hn) n.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
      (fun p hp => by
        have hd : p∣n := ((Nat.mem_primeFactors_of_ne_zero hn).mp hp).2
        exact_mod_cast hd)
    simpa only [Int.natAbs_natCast] using hh
  have hradR : ((∏ p∈n.primeFactors,p:ℕ):ℝ)≤(n:ℝ) := by exact_mod_cast hrad
  have hradpow := Real.rpow_le_rpow (by positivity) hradR hη.le
  have hs := hsupport.trans (mul_le_mul_of_nonneg_left hradpow
    (constant_pos _ _ (localConstant_one η hη)).le)
  have hh := hlocal.trans (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (by positivity) _))
  have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : η+η=δ := by dsimp [η];ring
  calc
    _ ≤ supportConstant (localConstant η) η*(n:ℝ)^η*(n:ℝ)^η := hh
    _ = divisorConstant δ*(n:ℝ)^δ := by rw [mul_assoc,←Real.rpow_add hnR,he];rfl

end ActualDivisorSubpower318
