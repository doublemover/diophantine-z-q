module
public import ActualOriginalGoodLayerNorm318
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public section
noncomputable section
namespace ActualOriginalNormEulerProduct318
open ActualOriginalGlobalCoefficient318 ActualOriginalGoodLayerNorm318
open ActualOriginalUnitLocalSeries318 ActualGoodPrimeDensityProduct318
open ActualOriginalAllPrimeFactors318 ActualOriginalLocalProductBounds318
open Filter
open scoped BigOperators Topology
set_option maxHeartbeats 16000000

@[expose] def localNormFactor (κ : ℤ) (p : ℕ) : ℝ :=
  if p.Prime then ∑' n, ‖coefficient κ (p^n)‖ else 1

lemma actual318_norm_local_summable (p : ℕ) (hp : p.Prime) :
    Summable (fun n => ‖coefficient 318 (p^n)‖) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa only [actual_coefficient_nonzero] using (actual318_unit_local_series p hp).1
lemma actual326_norm_local_summable (p : ℕ) (hp : p.Prime) :
    Summable (fun n => ‖coefficient 326 (p^n)‖) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa only [actual_coefficient_nonzero] using (actual326_unit_local_series p hp).1

lemma actual_norm_factor_ge_one (κ : ℤ)
    (hlocal : ∀ p, p.Prime → Summable (fun n => ‖coefficient κ (p^n)‖)) (p : ℕ) :
    1 ≤ localNormFactor κ p := by
  by_cases hp : p.Prime
  · rw [localNormFactor,if_pos hp]
    have h := (hlocal p hp).le_tsum 0 (fun n _ => norm_nonneg (coefficient κ (p^n)))
    simpa only [pow_zero,actual_coefficient_one,norm_one] using h
  · simp only [localNormFactor,if_neg hp,le_refl]

lemma actual_norm_factor_good (κ : ℤ) (p : ℕ) (hgood : Good κ p) :
    localNormFactor κ p = factor κ p := by
  letI : NeZero p := ⟨hgood.1.ne_zero⟩
  rw [localNormFactor,if_pos hgood.1,factor,if_pos hgood]
  exact (actual_good_norm_series κ p hgood.1 hgood.2.1 hgood.2.2).tsum_eq

/-- The norm Euler factors differ from the already controlled good-prime
factors at only the explicit finite exceptional set. Every exceptional norm
series is separately absolutely convergent; no positivity of its individual
complex coefficients is assumed. -/
theorem actual_norm_factor_product (κ : ℤ) (bad : Finset ℕ)
    (hcover : ∀ p, p ∉ bad → p.Prime → Good κ p)
    (hlocal : ∀ p, p.Prime → Summable (fun n => ‖coefficient κ (p^n)‖)) :
    ∃ S : ℝ, 0 < S ∧ HasProd (localNormFactor κ) S := by
  classical
  apply positive_product_of_error (localNormFactor κ)
  · intro p
    exact lt_of_lt_of_le zero_lt_one (actual_norm_factor_ge_one κ hlocal p)
  · apply (actual_good_prime_error_summable κ).congr_cofinite
    apply Filter.mem_cofinite.mpr
    apply bad.finite_toSet.subset
    intro p hp
    by_contra hbad
    apply hp
    have he : localNormFactor κ p = factor κ p := by
      by_cases hprime : p.Prime
      · exact actual_norm_factor_good κ p (hcover p hbad hprime)
      · have hng : ¬Good κ p := fun hh => hprime hh.1
        simp only [localNormFactor,factor,if_neg hprime,if_neg hng]
    rw [he]

lemma actual318_exception_cover (p : ℕ) (hn : p ∉ ({2,3,53} : Finset ℕ))
    (hp : p.Prime) : Good 318 p := by
  have h2 : p ≠ 2 := fun h => hn (by simp [h])
  have h3 : p ≠ 3 := fun h => hn (by simp [h])
  have h53 : p ≠ 53 := fun h => hn (by simp [h])
  exact ⟨hp,h2,original_318_good_remaining p hp h2 h3 h53⟩
lemma actual326_exception_cover (p : ℕ) (hn : p ∉ ({2,163} : Finset ℕ))
    (hp : p.Prime) : Good 326 p := by
  have h2 : p ≠ 2 := fun h => hn (by simp [h])
  have h163 : p ≠ 163 := fun h => hn (by simp [h])
  exact ⟨hp,h2,original_326_good_remaining p hp h2 h163⟩

theorem actual318_norm_euler_product : ∃ S : ℝ, 0<S ∧ HasProd (localNormFactor 318) S :=
  actual_norm_factor_product 318 {2,3,53} actual318_exception_cover actual318_norm_local_summable

theorem actual326_norm_euler_product : ∃ S : ℝ, 0<S ∧ HasProd (localNormFactor 326) S :=
  actual_norm_factor_product 326 {2,163} actual326_exception_cover actual326_norm_local_summable

lemma actual_norm_prime_cutoff (κ : ℤ) (N : ℕ) :
    (∏ p ∈ Nat.primesBelow N, ∑' n, ‖coefficient κ (p^n)‖) =
      partialProduct (localNormFactor κ) N := by
  classical
  simp only [Nat.primesBelow,Finset.prod_filter,partialProduct,localNormFactor]

/-- Uniform bounds on ALL finite norm Euler products, including cutoffs
before any exceptional prime, are constructed before the global series. -/
theorem actual_norm_cutoff_bound (κ : ℤ)
    (hlocal : ∀ p, p.Prime → Summable (fun n => ‖coefficient κ (p^n)‖))
    (hprod : ∃ S : ℝ, 0<S ∧ HasProd (localNormFactor κ) S) :
    ∃ U : ℝ, ∀ N, (∏ p ∈ Nat.primesBelow N, ∑' n, ‖coefficient κ (p^n)‖) ≤ U := by
  obtain ⟨S,hS,hprod⟩ := hprod
  obtain ⟨L,U,hL,hU,hbound⟩ := all_cutoff_bounds (localNormFactor κ)
    (fun p => lt_of_lt_of_le zero_lt_one (actual_norm_factor_ge_one κ hlocal p)) S hS hprod
  exact ⟨U,fun N => (actual_norm_prime_cutoff κ N).trans_le (hbound N).2⟩

end ActualOriginalNormEulerProduct318
