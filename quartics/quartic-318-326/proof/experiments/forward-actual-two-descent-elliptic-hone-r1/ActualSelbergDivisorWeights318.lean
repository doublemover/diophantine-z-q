module
public import ActualSelbergDivisorChoices318
public import OriginalWeightedSelberg318
public section
noncomputable section
namespace ActualSelbergDivisorWeights318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorChoices318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The genuine arithmetic-function Selberg term, independent of the
finite source only because the SAME original retainedDensity density is used. -/
@[expose] def terms (κ : ℤ) (γ : J → ℤ) (j₀ : J) : ArithmeticFunction ℝ :=
  (nu κ γ j₀).pmul (.prodPrimeFactors (fun p => (1-nu κ γ j₀ p)⁻¹))
lemma terms_eq_original (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    terms κ γ j₀=(OriginalWeightedSelberg318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).selbergTerms := rfl
lemma terms_multiplicative (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    (terms κ γ j₀).IsMultiplicative := by
  rw [terms_eq_original κ hκ γ hγ j₀ j₁ h0 h1 0 ∅]
  exact BoundingSieve.selbergTerms_isMultiplicative
lemma terms_prime (κ : ℤ) (γ : J → ℤ) (j₀ : J) (p : ℕ) (hp : p.Prime) :
    terms κ γ j₀ p=nu κ γ j₀ p/(1-nu κ γ j₀ p) := by
  simp only [terms,ArithmeticFunction.pmul_apply,
    ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,hp.primeFactors,
    Finset.prod_singleton,div_eq_mul_inv]

/-- Multiplicativity is applied to pairwise coprime optional ORIGINAL
primes, so the raw Euler weight is exactly the standard Selberg term. -/
lemma actual_modulus_weight (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ)
    (f : PrimeIndex κ γ N excluded → Bool) :
    terms κ γ j₀ (modulus κ γ N excluded f)=oddsWeight κ γ j₀ N excluded f := by
  have hm := terms_multiplicative κ hκ γ hγ j₀ j₁ h0 h1
  have hc : (↑(Finset.univ : Finset (PrimeIndex κ γ N excluded)) : Set _).Pairwise
      (fun i j => Nat.Coprime (if f i then i.1 else 1) (if f j then j.1 else 1)) := by
    intro i _ j _ hij
    cases hi : f i <;> cases hj : f j <;> simp only [hi,hj,Bool.false_eq_true,if_false,if_true]
    · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_right _
    · apply (Nat.coprime_primes
        (retained_facts κ γ N excluded i.1 i.2).1.1
        (retained_facts κ γ N excluded j.1 j.2).1.1).mpr
      exact fun h => hij (Subtype.ext h)
  unfold modulus oddsWeight
  rw [hm.map_prod _ _ hc]
  apply Finset.prod_congr rfl
  intro i _
  cases hi : f i
  · simpa only [hi,Bool.false_eq_true,if_false] using hm.map_one
  · simp only [hi,if_true,retainedDensity]
    exact terms_prime κ γ j₀ i.1 (retained_facts κ γ N excluded i.1 i.2).1.1

@[expose] def denominator (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ) (z : ℝ) : ℝ :=
  ∑ d∈(product κ γ N excluded).divisors,if (d:ℝ)<z then terms κ γ j₀ d else 0

/-- Exact strict-divisor denominator identity. Surjectivity onto ALL
retained-product divisors prevents silently replacing the sieve sum by
an unrelated choice sum; injectivity prevents multiplicity inflation. -/
theorem actual_denominator_eq_truncated (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) :
    denominator κ γ j₀ N excluded z=truncated κ γ j₀ N excluded z := by
  classical
  have he := Equiv.sum_comp (divisorEquiv κ γ N excluded)
    (fun d : ↥(product κ γ N excluded).divisors =>
      if (d.1:ℝ)<z then terms κ γ j₀ d.1 else 0)
  rw [Finset.sum_coe_sort] at he
  unfold denominator truncated
  rw [←he]
  apply Finset.sum_congr rfl
  intro f _
  change (if (modulus κ γ N excluded f:ℝ)<z then
      terms κ γ j₀ (modulus κ γ N excluded f) else 0)=_
  rw [actual_modulus_weight κ hκ γ hγ j₀ j₁ h0 h1]

end ActualSelbergDivisorWeights318
