module
public import ActualSieveDensityPositive318
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public section
noncomputable section
namespace ActualSieveMultiplicativeDensity318
open scoped BigOperators
open ActualSieveEulerProduct318
set_option maxHeartbeats 2000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def localDensity (κ : ℤ) (γ : J → ℤ) (j₀ : J) (p : ℕ) : ℝ :=
  if hp : p.Prime then (OriginalSieveCRTProduct318.densityAt p hp κ γ j₀:ℝ) else 0
@[expose] def nu (κ : ℤ) (γ : J → ℤ) (j₀ : J) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (localDensity κ γ j₀)

/-- Actual multiplicative extension of the original local densities. -/
theorem nu_multiplicative (κ : ℤ) (γ : J → ℤ) (j₀ : J) : (nu κ γ j₀).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem nu_at_prime (κ : ℤ) (γ : J → ℤ) (j₀ : J) (p : ℕ) (hp : p.Prime) :
    nu κ γ j₀ p=(OriginalSieveCRTProduct318.densityAt p hp κ γ j₀:ℝ) := by
  simp only [nu,ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors,
    Finset.prod_singleton,localDensity,dif_pos hp]

/-- Literal cutoff prime set; exceptional and insufficiently large primes
are removed by the previously constructed original-data predicate. -/
@[expose] def selected (κ : ℤ) (γ : J → ℤ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (Eligible κ γ)
@[expose] def primeProduct (κ : ℤ) (γ : J → ℤ) (N : ℕ) : ℕ :=
  ∏ p∈selected κ γ N, p

lemma selected_eligible (κ : ℤ) (γ : J → ℤ) (N p : ℕ) (hp : p∈selected κ γ N) :
    Eligible κ γ p := (Finset.mem_filter.mp hp).2
lemma selected_prime (κ : ℤ) (γ : J → ℤ) (N p : ℕ) (hp : p∈selected κ γ N) : p.Prime :=
  (selected_eligible κ γ N p hp).1
lemma product_ne_zero (κ : ℤ) (γ : J → ℤ) (N : ℕ) : primeProduct κ γ N≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (selected_prime κ γ N p hp).ne_zero

/-- Squarefreeness is constructed from distinct literal cutoff primes. -/
theorem product_squarefree (κ : ℤ) (γ : J → ℤ) (N : ℕ) :
    Squarefree (primeProduct κ γ N) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (selected_prime κ γ N p hp) (selected_prime κ γ N q hq)).mpr hpq)
  · intro p hp
    exact (selected_prime κ γ N p hp).squarefree

theorem prime_dvd_product_iff (κ : ℤ) (γ : J → ℤ) (N p : ℕ) (hp : p.Prime) :
    p∣primeProduct κ γ N ↔ p∈selected κ γ N := by
  have he : (primeProduct κ γ N).primeFactors=selected κ γ N :=
    Nat.primeFactors_prod (selected_prime κ γ N)
  rw [←he,Nat.mem_primeFactors_of_ne_zero (product_ne_zero κ γ N)]
  simp only [hp,true_and]

/-- Both strict Selberg density hypotheses are produced at every divisor
prime of the actually constructed cutoff product. -/
theorem actual_prime_bounds (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N p : ℕ)
    (hp : p.Prime) (hd : p∣primeProduct κ γ N) :
    0<nu κ γ j₀ p ∧ nu κ γ j₀ p<1 := by
  have hm := (prime_dvd_product_iff κ γ N p hp).mp hd
  have hel := selected_eligible κ γ N p hm
  rw [nu_at_prime κ γ j₀ p hp]
  exact ActualSieveDensityPositive318.eligible_density_bounds κ hκ γ hγ j₀ j₁ h0 h1 p hel

end ActualSieveMultiplicativeDensity318
