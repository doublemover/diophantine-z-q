module
public import ActualPrimitiveNonnegativeSieve318
public section
noncomputable section
namespace ActualPrimitiveOptimizedPrimeBound318
open scoped BigOperators
open QuadricCRTAssembly318 ActualPrimitiveSourceRestriction318 ActualPrimePointPrimitivity318
open ActualPrimitiveNonnegativeSieve318 OriginalPrimeWeightedSieve318 OriginalWeightedSelberg318
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergCoefficients318 ActualOptimalSelbergBound318
set_option maxHeartbeats 24000000
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma prime_point_removed_survives (κ : ℤ) (γ : J → ℤ) (N excluded : ℕ)
    (v : Quadric κ) (hv : PrimePoint κ γ N v) :
    Nat.Coprime (product κ γ N excluded) (key κ γ v) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  have hs := (Finset.mem_erase.mp i.2).2
  have hd : i.1∣primeProduct κ γ N := Finset.dvd_prod_of_mem _ hs
  exact Nat.Coprime.of_dvd_left hd (prime_point_survives κ γ N v hv)

/-- The complete original prime-point mass is bounded by the globally
primitive source sieve, for ANY actual nonnegative point weight.
Primitivity is constructed from prime form values, not assumed. -/
theorem actual_prime_mass_le_sifted (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (S : Finset (Quadric κ)) (w : Quadric κ → ℝ) (hw : ∀v,0≤w v) :
    (∑v∈S,if PrimePoint κ γ N v then w v else 0)≤
      (ActualPrimitiveNonnegativeSieve318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw).siftedSum := by
  classical
  rw [ActualPrimitiveNonnegativeSieve318.actual_sifted_sum,primitiveSource,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : PrimePoint κ γ N v
  · rw [if_pos hv,if_pos (original_prime_point_primitive κ γ j₀ N v hv),
      if_pos (prime_point_removed_survives κ γ N excluded v hv)]
  · rw [if_neg hv]
    split_ifs <;> first | exact hw v | exact le_rfl

/-- Produced logarithmic prime-point upper bound on the correct globally
primitive source. The constant precedes N, removal, source and weight.
The error belongs to THIS exact weight, not the earlier product-log one.
Taking w=1 gives the actual unweighted prime count; smooth weights may
be supplied when constructing the genuine analytic congruence theorem. -/
theorem original_primitive_prime_log_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ,0<C ∧ ∀ N,2≤N → ∀ excluded : ℕ,
      ∀ S : Finset (Quadric κ),∀ w : Quadric κ → ℝ,∀ hw : ∀v,0≤w v,
      (∑v∈S,if PrimePoint κ γ N v then w v else 0)≤
        C*(∑v∈primitiveSource κ S,w v)/(Real.log (N:ℝ))^(Fintype.card J)+
        (ActualPrimitiveNonnegativeSieve318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw).errSum
          (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded (threshold J N))) := by
  classical
  obtain ⟨C,hC,hmain⟩ := ActualSelbergLogDenominator318.actual_optimizer_log_bound
    κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨C,hC,?_⟩
  intro N hN excluded S w hw
  let s := ActualPrimitiveNonnegativeSieve318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw
  let λ := coefficients κ γ j₀ N excluded (threshold J N)
  have hλ := actual_coefficient_one κ hκ γ hγ j₀ j₁ h0 h1 N excluded _
    (threshold_gt_one N (by omega))
  have hs := @BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius s
    (BoundingSieve.lambdaSquared λ) (BoundingSieve.upperMoebius_lambdaSquared _ hλ)
  have hm : s.mainSum (BoundingSieve.lambdaSquared λ)≤C/(Real.log (N:ℝ))^(Fintype.card J) := by
    rw [ActualPrimitiveNonnegativeSieve318.actual_main_sum_identity]
    exact hmain N hN excluded (primitiveSource κ S)
  have hmass : 0≤s.totalMass := Finset.sum_nonneg (fun v _ => hw v)
  have ht := mul_le_mul_of_nonneg_left hm hmass
  have hh := (actual_prime_mass_le_sifted κ hκ γ hγ j₀ j₁ h0 h1 N excluded S w hw).trans
    (hs.trans (add_le_add_right ht _))
  convert hh using 1 <;> dsimp only [s,ActualPrimitiveNonnegativeSieve318.sieve] <;> ring

end ActualPrimitiveOptimizedPrimeBound318
