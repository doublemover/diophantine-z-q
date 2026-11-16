module
public import ActualSievePrimeMoment318
public section
noncomputable section
namespace ActualTruncatedSelbergEuler318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 FiniteBernoulliEulerMoment318
set_option maxHeartbeats 18000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def PrimeIndex (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) := ↥(retained κ γ N excluded)
@[expose] def retainedDensity (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (i : PrimeIndex κ γ N excluded) : ℝ := nu κ γ j₀ i.1
@[expose] def logPrime (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (i : PrimeIndex κ γ N excluded) : ℝ := Real.log (i.1:ℝ)
@[expose] def modulus (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) : ℕ := ∏ i,if f i then i.1 else 1
@[expose] def product (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) : ℕ :=
  ∏ i : PrimeIndex κ γ N excluded,i.1

lemma modulus_pos (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) : 0<modulus κ γ N excluded f := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (retained_facts κ γ N excluded i.1 i.2).1.1.pos
  · norm_num
lemma modulus_dvd (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) : modulus κ γ N excluded f∣product κ γ N excluded := by
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  split_ifs
  · exact dvd_rfl
  · exact one_dvd _

lemma prime_dvd_modulus (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) (i : PrimeIndex κ γ N excluded) :
    i.1∣modulus κ γ N excluded f ↔ f i=true := by
  have hi := (retained_facts κ γ N excluded i.1 i.2).1.1
  constructor
  · intro hd
    obtain ⟨j,_,hj⟩ := (hi.prime.dvd_finsetProd_iff _).mp hd
    cases hfj : f j with
    | false =>
      have hbad : i.1∣1 := by simpa only [hfj,Bool.false_eq_true,if_false] using hj
      exact False.elim (hi.ne_one (Nat.eq_one_of_dvd_one hbad))
    | true =>
      have hdiv : i.1∣j.1 := by simpa only [hfj,if_true] using hj
      have hpj := (retained_facts κ γ N excluded j.1 j.2).1.1
      have he : i.1=j.1 := (hpj.dvd_iff_eq hi.ne_one).mp hdiv
      have hij : i=j := Subtype.ext he
      simpa only [hij] using hfj
  · intro hf
    have hd := Finset.dvd_prod_of_mem (fun j : PrimeIndex κ γ N excluded => if f j then j.1 else 1)
      (Finset.mem_univ i)
    simpa only [hf,if_true] using hd

/-- Distinct prime choices give distinct ACTUAL integer divisors, so the
truncated Euler sum below does not duplicate squarefree moduli. -/
lemma modulus_injective (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ) :
    Function.Injective (modulus κ γ N excluded) := by
  intro f g he
  funext i
  have hh : (f i=true)↔(g i=true) := by
    rw [←prime_dvd_modulus,he,prime_dvd_modulus]
  cases hf : f i <;> cases hg : g i <;> simp_all

/-- The additive cost is the logarithm of this SAME integer product. -/
lemma actual_log_modulus (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) :
    Real.log (modulus κ γ N excluded f:ℝ)=cost (logPrime κ γ N excluded) f := by
  rw [modulus,Nat.cast_prod,Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    cases hf : f i <;> simp [hf,logPrime]
  · intro i _
    cases hf : f i
    · simp [hf]
    · have hp := (retained_facts κ γ N excluded i.1 i.2).1.1.ne_zero
      simpa only [hf,if_true] using (show (i.1:ℝ)≠0 by exact_mod_cast hp)

@[expose] def euler (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) : ℝ :=
  ∏ i : PrimeIndex κ γ N excluded,1/(1-retainedDensity κ γ j₀ N excluded i)
@[expose] def oddsWeight (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) : ℝ :=
  ∏ i,if f i then retainedDensity κ γ j₀ N excluded i/(1-retainedDensity κ γ j₀ N excluded i) else 1
@[expose] def truncated (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) (z : ℝ) : ℝ :=
  ∑ f : PrimeIndex κ γ N excluded → Bool,
    if (modulus κ γ N excluded f:ℝ)<z then oddsWeight κ γ j₀ N excluded f else 0

lemma probability_to_odds (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) :
    euler κ γ j₀ N excluded*probability (retainedDensity κ γ j₀ N excluded) f=
      oddsWeight κ γ j₀ N excluded f := by
  rw [euler,probability,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hq := retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded i
  have hn : 1-retainedDensity κ γ j₀ N excluded i≠0 := by dsimp [retainedDensity];linarith
  cases hf : f i <;> dsimp [factor]
  · simp only [hf,Bool.false_eq_true,if_false]
    field_simp [hn]
  · simp only [hf,if_true]
    ring

lemma actual_truncation_identity (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ) (hz : 0<z) :
    truncated κ γ j₀ N excluded z=
      euler κ γ j₀ N excluded*
        shortMass (retainedDensity κ γ j₀ N excluded) (logPrime κ γ N excluded) (Real.log z) := by
  unfold truncated shortMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  have hm : (0:ℝ)<modulus κ γ N excluded f := by exact_mod_cast modulus_pos κ γ N excluded f
  have he : cost (logPrime κ γ N excluded) f<Real.log z ↔ (modulus κ γ N excluded f:ℝ)<z := by
    rw [←actual_log_modulus]
    exact Real.log_lt_log_iff hm hz
  by_cases hh : (modulus κ γ N excluded f:ℝ)<z
  · rw [if_pos hh,if_pos (he.mpr hh)]
    exact (probability_to_odds κ hκ γ hγ j₀ j₁ h0 h1 N excluded f).symm
  · rw [if_neg hh,if_neg (fun h => hh (he.mp h)),mul_zero]

/-- A concrete polynomial-scale truncation threshold, built from the
actual Chebyshev moment bound. No moment/cutoff hypothesis is left open. -/
@[expose] def logThreshold (J : Type*) [Fintype J] (N : ℕ) : ℝ := 1+2*momentBound J N
@[expose] def threshold (J : Type*) [Fintype J] (N : ℕ) : ℝ := Real.exp (logThreshold J N)

/-- At least half of the ACTUAL original Euler mass lies on distinct
integer divisors d<threshold. The bound is uniform in the removed prime;
the Euler product still retains that explicit removal. -/
theorem actual_half_euler_truncation (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ) (hN : 1≤N) (excluded : ℕ) :
    euler κ γ j₀ N excluded/2≤truncated κ γ j₀ N excluded (threshold J N) := by
  have hq (i : PrimeIndex κ γ N excluded) :
      0≤retainedDensity κ γ j₀ N excluded i ∧ retainedDensity κ γ j₀ N excluded i≤1 := by
    have hh := retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded i
    exact ⟨hh.1.le,hh.2.trans (by norm_num)⟩
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hM : 0≤momentBound J N := by
    have hC := (momentConstant_pos (J := J)).le
    have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    dsimp [momentBound]
    positivity
  have hL : 0<logThreshold J N := by dsimp [logThreshold];linarith
  have hm : (∑ i : PrimeIndex κ γ N excluded,
      retainedDensity κ γ j₀ N excluded i*logPrime κ γ N excluded i)≤logThreshold J N/2 := by
    have hh := actual_moment_bound κ hκ γ hγ j₀ j₁ h0 h1 N hN excluded
    have he : (∑ i : PrimeIndex κ γ N excluded,
      retainedDensity κ γ j₀ N excluded i*logPrime κ γ N excluded i)=moment κ γ j₀ N excluded := by
      simp only [PrimeIndex,retainedDensity,logPrime,Finset.sum_coe_sort,moment]
    rw [he]
    dsimp [logThreshold]
    linarith
  have hs := actual_half_mass (retainedDensity κ γ j₀ N excluded) (logPrime κ γ N excluded) hq
    (fun i => Real.log_natCast_nonneg i.1) (logThreshold J N) hL hm
  have hE : 0≤euler κ γ j₀ N excluded := by
    apply Finset.prod_nonneg
    intro i _
    have hh := retained_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 N excluded i
    have hd : 0<1-retainedDensity κ γ j₀ N excluded i := by
      dsimp [retainedDensity]
      linarith [hh.2]
    exact (div_pos (by norm_num) hd).le
  rw [actual_truncation_identity κ hκ γ hγ j₀ j₁ h0 h1 N excluded _ (Real.exp_pos _)]
  rw [threshold,Real.log_exp]
  have hh := mul_le_mul_of_nonneg_left hs hE
  simpa only [mul_one_div] using hh

/-- Explicit polynomial scale of the constructed cutoff. This is the
same threshold used in the actual strict-divisor truncation above. -/
theorem threshold_polynomial (N : ℕ) (hN : 1≤N) :
    threshold J N=Real.exp (1+2*momentConstant J*Real.log 4)*
      (N:ℝ)^(2*momentConstant J*Real.log 4) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  unfold threshold
  rw [Real.rpow_def_of_pos hn]
  rw [←Real.exp_add]
  congr 1
  dsimp [logThreshold,momentBound]
  ring

end ActualTruncatedSelbergEuler318
