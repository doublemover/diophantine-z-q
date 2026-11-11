module
public import FiniteMobiusCoefficientBound318
public section
noncomputable section
namespace ActualSievePolynomialDensity318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorChoices318 ActualSieveEulerProduct318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual local numerator is a positive INTEGER cardinality.
Consequently nu(p)*p^4>=1, including the two-form inert case where the
first-order reciprocal-prime term vanishes. -/
lemma actual_prime_polynomial_lower (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (p : ℕ) (hp : Eligible κ γ p) : 1≤nu κ γ j₀ p*(p:ℝ)^4 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨hp2,hkp,_⟩ := FixedSieveExceptionalPrimes318.outside_conditions
    κ hκ γ hγ p hp.1 hp.2.1
  let A := Nat.card (OriginalSieveCRTProduct318.badSet (κ:ZMod p) (fun j => (γ j:ZMod p)))
  let D : ℕ := p^4-1
  have hq := OriginalSieveCRTProduct318.local_density p hp2 κ hkp γ j₀
  have he : (A:ℝ)/(D:ℝ)=nu κ γ j₀ p := by
    rw [nu_at_prime κ γ j₀ p hp.1]
    change (A:ℝ)/(D:ℝ)=
      (FiniteSieveDensity318.density (κ:ZMod p) (fun j => (γ j:ZMod p)) j₀:ℝ)
    exact_mod_cast hq
  have hν : 0<nu κ γ j₀ p := by
    rw [nu_at_prime κ γ j₀ p hp.1]
    exact (ActualSieveDensityPositive318.eligible_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 p hp).1
  have hA : 1≤A := by
    by_contra h
    have hz : A=0 := by omega
    rw [hz,Nat.cast_zero,zero_div] at he
    linarith
  have hD : 0<D := by
    have hpN := hp.1.two_le
    have hpow : 1<p^4 := by
      exact one_lt_pow₀ (by omega : (1:ℕ)<p) (by norm_num : (4:ℕ)≠0)
    dsimp [D]
    omega
  have hDR : (0:ℝ)<D := by exact_mod_cast hD
  have hmul : (A:ℝ)=nu κ γ j₀ p*(D:ℝ) := (div_eq_iff₀ hDR.ne').mp he
  have hAle : (1:ℝ)≤A := by exact_mod_cast hA
  have hDle : (D:ℝ)≤(p:ℝ)^4 := by exact_mod_cast (Nat.sub_le (p^4) 1)
  calc
    1 ≤ (A:ℝ) := hAle
    _ = nu κ γ j₀ p*(D:ℝ) := hmul
    _ ≤ _ := mul_le_mul_of_nonneg_left hDle hν.le

/-- Multiplication on the ACTUAL squarefree retained divisor gives a
uniform polynomial reciprocal-density bound. No lower first-order
density or unproved prime distribution estimate is used. -/
lemma actual_divisor_polynomial_lower (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded d : ℕ) (hd : d∣product κ γ N excluded) :
    1≤nu κ γ j₀ d*(d:ℝ)^4 := by
  have hs := Squarefree.squarefree_of_dvd hd
    (ActualSelbergDivisorChoices318.product_squarefree κ γ N excluded)
  have hp : (∏ p∈d.primeFactors,p)=d := Nat.prod_primeFactors_of_squarefree hs
  have hν : (∏ p∈d.primeFactors,nu κ γ j₀ p)=nu κ γ j₀ d := by
    rw [←(nu_multiplicative κ γ j₀).map_prod_of_subset_primeFactors d _ Finset.Subset.rfl,hp]
  have hcast : (∏ p∈d.primeFactors,(p:ℝ))=(d:ℝ) := by exact_mod_cast hp
  calc
    1 ≤ ∏ p∈d.primeFactors,nu κ γ j₀ p*(p:ℝ)^4 := by
      apply Finset.one_le_prod
      intro p hpd
      have hprime := Nat.prime_of_mem_primeFactors hpd
      have hret := (ActualSelbergDivisorChoices318.prime_dvd_product_iff κ γ N excluded p hprime).mp
        ((Nat.dvd_of_mem_primeFactors hpd).trans hd)
      exact actual_prime_polynomial_lower κ hκ γ hγ j₀ j₁ h0 h1 p
        (retained_facts κ γ N excluded p hret).1
    _ = nu κ γ j₀ d*(d:ℝ)^4 := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow,hν,hcast]

end ActualSievePolynomialDensity318
