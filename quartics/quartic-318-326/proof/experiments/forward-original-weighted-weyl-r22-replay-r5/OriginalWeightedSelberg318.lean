module
public import ActualSieveMultiplicativeDensity318
public section
noncomputable section
namespace OriginalWeightedSelberg318
open scoped BigOperators
open QuadricCRTAssembly318 ActualSieveMultiplicativeDensity318
set_option maxHeartbeats 2000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Original prime-form value on the actual five-coordinate source. -/
@[expose] def form (κ : ℤ) (γ : J → ℤ) (j : J) (v : Quadric κ) : ℤ :=
  v.1.1.1^2+v.1.1.2^2+γ j*v.1.2.2^2
@[expose] def key (κ : ℤ) (γ : J → ℤ) (v : Quadric κ) : ℕ :=
  ∏ j, (form κ γ j v).natAbs
/-- Clipping at1 makes weights nonnegative on the entire actual box. At
prime-form values this is exactly the original product of logarithms. -/
@[expose] def weight (κ : ℤ) (γ : J → ℤ) (v : Quadric κ) : ℝ :=
  ∏ j, Real.log (max 1 ((form κ γ j v).natAbs:ℝ))

lemma weight_nonneg (κ : ℤ) (γ : J → ℤ) (v : Quadric κ) : 0≤weight κ γ v := by
  apply Finset.prod_nonneg
  intro j hj
  exact Real.log_nonneg (le_max_left _ _)

theorem weight_at_prime_values (κ : ℤ) (γ : J → ℤ) (v : Quadric κ)
    (hp : ∀ j, (form κ γ j v).natAbs.Prime) :
    weight κ γ v=∏ j, Real.log ((form κ γ j v).natAbs:ℝ) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hh : (1:ℝ)≤(form κ γ j v).natAbs := by
    have h := (hp j).two_le
    exact_mod_cast (show 1≤(form κ γ j v).natAbs by omega)
  rw [max_eq_right hh]

/-- Multiple original points can have the same key. Their weights are
summed, never deduplicated by replacing the point set with its image. -/
@[expose] def fiberWeight (κ : ℤ) (γ : J → ℤ) (S : Finset (Quadric κ)) (n : ℕ) : ℝ := by
  classical
  exact ∑ v∈S.filter (fun v => key κ γ v=n), weight κ γ v

lemma fiberWeight_nonneg (κ : ℤ) (γ : J → ℤ) (S : Finset (Quadric κ)) (n : ℕ) :
    0≤fiberWeight κ γ S n := by
  classical
  apply Finset.sum_nonneg
  intro v hv
  exact weight_nonneg κ γ v

/-- Exact fiber recombination, preserving every original point's weight. -/
lemma fiber_sum (κ : ℤ) (γ : J → ℤ) (S : Finset (Quadric κ)) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ n∈S.image (key κ γ), if P n then fiberWeight κ γ S n else 0)=
      ∑ v∈S, if P (key κ γ v) then weight κ γ v else 0 := by
  classical
  calc
    _ = ∑ n∈S.image (key κ γ), ∑ v∈S.filter (fun v => key κ γ v=n),
        if P (key κ γ v) then weight κ γ v else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : P n
      · simp only [hp,ite_true,fiberWeight]
        apply Finset.sum_congr rfl
        intro v hv
        have he := (Finset.mem_filter.mp hv).2
        simp only [he,hp,ite_true]
      · simp only [hp,ite_false]
        symm
        apply Finset.sum_eq_zero
        intro v hv
        have he := (Finset.mem_filter.mp hv).2
        simp only [he,hp,ite_false]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun v hv => Finset.mem_image_of_mem (key κ γ) hv) _

/-- A completely constructed Selberg data object for any finite portion
of the ORIGINAL quadric, with actual local densities and original weights.
No remainder estimate or prime asymptotic is assumed in this definition. -/
@[expose] def sieve (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ)
    (S : Finset (Quadric κ)) : BoundingSieve := by
  classical
  exact {
    support := S.image (key κ γ)
    prodPrimes := primeProduct κ γ N
    prodPrimes_squarefree := product_squarefree κ γ N
    weights := fiberWeight κ γ S
    weights_nonneg := fiberWeight_nonneg κ γ S
    totalMass := ∑ v∈S, weight κ γ v
    nu := nu κ γ j₀
    nu_mult := nu_multiplicative κ γ j₀
    nu_pos_of_prime := fun p hp hd => (actual_prime_bounds κ hκ γ hγ j₀ j₁ h0 h1 N p hp hd).1
    nu_lt_one_of_prime := fun p hp hd => (actual_prime_bounds κ hκ γ hγ j₀ j₁ h0 h1 N p hp hd).2 }

/-- The sifted sum is exactly the sum over ORIGINAL source points. -/
theorem actual_sifted_sum (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ)
    (S : Finset (Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).siftedSum=
      ∑ v∈S, if Nat.Coprime (primeProduct κ γ N) (key κ γ v) then weight κ γ v else 0 := by
  classical
  exact fiber_sum κ γ S (Nat.Coprime (primeProduct κ γ N))

/-- Every divisor remainder also refers to the original weighted points. -/
theorem actual_divisor_mass (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ)
    (S : Finset (Quadric κ)) (d : ℕ) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).multSum d=
      ∑ v∈S, if d∣key κ γ v then weight κ γ v else 0 := by
  classical
  exact fiber_sum κ γ S (fun n => d∣n)

/-- The actual weighted source now supports the genuine Lambda-squared
upper bound. Remainders remain their EXACT original finite sums; this does
not assert the quantitative remainder bound still needed for transference. -/
theorem actual_lambda_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ)
    (S : Finset (Quadric κ)) (λ : ℕ → ℝ) (hλ : λ 1=1) :
    let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N S
    s.siftedSum≤s.totalMass*s.mainSum (BoundingSieve.lambdaSquared λ)+
      s.errSum (BoundingSieve.lambdaSquared λ) := by
  apply BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
  exact BoundingSieve.upperMoebius_lambdaSquared λ hλ

/-- Actual original weighted-point Lambda-squared bound. The remainder
is not assumed small and is not silently replaced by a CRT residue count. -/
theorem original_weighted_upper_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (S : Finset (Quadric κ)) (λ : ℕ → ℝ) (hλ : λ 1=1) :
    (∑ v∈S, if Nat.Coprime (primeProduct κ γ N) (key κ γ v) then weight κ γ v else 0)≤
      (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).totalMass*
        (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).mainSum (BoundingSieve.lambdaSquared λ)+
        (sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).errSum (BoundingSieve.lambdaSquared λ) := by
  rw [←actual_sifted_sum κ hκ γ hγ j₀ j₁ h0 h1 N S]
  exact actual_lambda_bound κ hκ γ hγ j₀ j₁ h0 h1 N S λ hλ

end OriginalWeightedSelberg318
