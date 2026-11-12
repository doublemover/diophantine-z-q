module
public import OriginalWeightedSelberg318
public section
noncomputable section
namespace OriginalPrimeWeightedSieve318
open scoped BigOperators
open QuadricCRTAssembly318 OriginalWeightedSelberg318 ActualSieveMultiplicativeDensity318
set_option maxHeartbeats 2000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Literal positive prime values, beyond the actual sieve cutoff. -/
@[expose] def PrimePoint (κ : ℤ) (γ : J → ℤ) (N : ℕ) (v : Quadric κ) : Prop :=
  ∀ j, 0<form κ γ j v ∧ (form κ γ j v).natAbs.Prime ∧ N≤(form κ γ j v).natAbs

/-- Original simultaneous prime points really survive the constructed sieve.
The bound p<N for cutoff primes is used explicitly, not a primality oracle. -/
theorem prime_point_survives (κ : ℤ) (γ : J → ℤ) (N : ℕ) (v : Quadric κ)
    (hv : PrimePoint κ γ N v) : Nat.Coprime (primeProduct κ γ N) (key κ γ v) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hprime := selected_prime κ γ N p hp
  apply hprime.coprime_iff_not_dvd.mpr
  intro hd
  have hd' : p∣∏ j, (form κ γ j v).natAbs := hd
  obtain ⟨j,hj,hdiv⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hd'
  have he := ((hv j).2.1.dvd_iff_eq hprime.ne_one).mp hdiv
  have hlarge := (hv j).2.2
  have hsmall : p<N := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  omega

/-- On these actual positive prime points the source weight is exactly
product log(original integer form), with no absolute-value/clipping change. -/
theorem prime_point_weight (κ : ℤ) (γ : J → ℤ) (N : ℕ) (v : Quadric κ)
    (hv : PrimePoint κ γ N v) :
    weight κ γ v=∏ j, Real.log (form κ γ j v:ℝ) := by
  rw [weight_at_prime_values κ γ v (fun j => (hv j).2.1)]
  apply Finset.prod_congr rfl
  intro j hj
  have he : ((form κ γ j v).natAbs:ℤ)=form κ γ j v := by
    rw [Int.natCast_natAbs,abs_of_pos (hv j).1]
  have hr : ((form κ γ j v).natAbs:ℝ)=(form κ γ j v:ℝ) := by exact_mod_cast he
  rw [hr]

/-- Exact original positive-prime logarithmic sum, not a count of residue
classes or the image of the key map. -/
@[expose] def primeWeightedSum (κ : ℤ) (γ : J → ℤ) (N : ℕ)
    (S : Finset (Quadric κ)) : ℝ := by
  classical
  exact ∑ v∈S, if PrimePoint κ γ N v then ∏ j, Real.log (form κ γ j v:ℝ) else 0

theorem prime_weighted_le_sifted (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (S : Finset (Quadric κ)) :
    primeWeightedSum κ γ N S≤(sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).siftedSum := by
  classical
  rw [actual_sifted_sum]
  apply Finset.sum_le_sum
  intro v hvS
  by_cases hv : PrimePoint κ γ N v
  · rw [if_pos hv,if_pos (prime_point_survives κ γ N v hv),prime_point_weight κ γ N v hv]
  · rw [if_neg hv]
    split_ifs
    · exact weight_nonneg κ γ v
    · exact le_rfl

/-- Genuine original simultaneous-prime weighted upper bound, with exact
integer-point remainders still displayed rather than assumed small. -/
theorem prime_weighted_lambda_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (S : Finset (Quadric κ)) (λ : ℕ → ℝ) (hλ : λ 1=1) :
    primeWeightedSum κ γ N S≤
      (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).totalMass*
        (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).mainSum (BoundingSieve.lambdaSquared λ)+
        (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).errSum (BoundingSieve.lambdaSquared λ) :=
  (prime_weighted_le_sifted κ hκ γ hγ j₀ j₁ h0 h1 N S).trans
    (actual_lambda_bound κ hκ γ hγ j₀ j₁ h0 h1 N S λ hλ)

end OriginalPrimeWeightedSieve318
