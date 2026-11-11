module
public import ActualOriginalNormEulerProduct318
public section
noncomputable section
namespace ActualOriginalGlobalSeriesSummable318
open ActualOriginalGlobalCoefficient318 ActualOriginalNormEulerProduct318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Local absolute convergence and produced bounded finite norm Euler
products imply absolute convergence over ALL denominators. The comparison
uses exact smooth-number sums and includes every finite prefix before
passing to the global sum. -/
theorem actual_global_norm_summable_of_cutoffs (κ : ℤ)
    (hlocal : ∀ p, p.Prime → Summable (fun n => ‖coefficient κ (p^n)‖))
    (hbound : ∃ U : ℝ, ∀ N,
      (∏ p ∈ Nat.primesBelow N, ∑' n, ‖coefficient κ (p^n)‖) ≤ U) :
    Summable (fun q => ‖coefficient κ q‖) := by
  classical
  obtain ⟨U,hU⟩ := hbound
  apply summable_of_sum_range_le (fun q => norm_nonneg (coefficient κ q))
  intro N
  have h1 : ‖coefficient κ 1‖ = 1 := by rw [actual_coefficient_one,norm_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n →
      ‖coefficient κ (m*n)‖ = ‖coefficient κ m‖*‖coefficient κ n‖ := by
    intro m n h
    rw [actual_coefficient_coprime κ h,norm_mul]
  have hlocal' : ∀ {p : ℕ}, p.Prime → Summable (fun n => ‖‖coefficient κ (p^n)‖‖) := by
    intro p hp
    simpa only [norm_norm] using hlocal p hp
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f:=fun q => ‖coefficient κ q‖) h1 hmul hlocal' N).2
  have hi : HasSum ((Nat.smoothNumbers N).indicator (fun q => ‖coefficient κ q‖))
      (∏ p ∈ Nat.primesBelow N, ∑' n, ‖coefficient κ (p^n)‖) :=
    hasSum_subtype_iff_indicator.mp hs
  have hnonneg (q : ℕ) : 0 ≤ (Nat.smoothNumbers N).indicator (fun j => ‖coefficient κ j‖) q := by
    by_cases hq : q ∈ Nat.smoothNumbers N
    · rw [Set.indicator_of_mem hq]
      exact norm_nonneg _
    · simp only [Set.indicator_of_notMem hq,le_refl]
  have hle := hi.summable.sum_le_tsum (Finset.range N) (fun q _ => hnonneg q)
  have he : (∑ q ∈ Finset.range N, ‖coefficient κ q‖) =
      ∑ q ∈ Finset.range N, (Nat.smoothNumbers N).indicator (fun j => ‖coefficient κ j‖) q := by
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hq0 : q=0
    · subst q
      simp [actual_coefficient_zero]
    · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
        (Nat.pos_of_ne_zero hq0) (Finset.mem_range.mp hq))]
  have hle' : (∑ q ∈ Finset.range N,
      (Nat.smoothNumbers N).indicator (fun j => ‖coefficient κ j‖) q) ≤
      ∏ p ∈ Nat.primesBelow N, ∑' n, ‖coefficient κ (p^n)‖ := by
    simpa only [hi.tsum_eq] using hle
  exact he.trans_le (hle'.trans (hU N))

/-- Absolute convergence of the literal global unit-frequency
singular series for318, with the zero denominator excluded explicitly. -/
theorem actual318_global_norm_summable : Summable (fun q => ‖coefficient 318 q‖) :=
  actual_global_norm_summable_of_cutoffs 318 actual318_norm_local_summable
    (actual_norm_cutoff_bound 318 actual318_norm_local_summable actual318_norm_euler_product)

theorem actual326_global_norm_summable : Summable (fun q => ‖coefficient 326 q‖) :=
  actual_global_norm_summable_of_cutoffs 326 actual326_norm_local_summable
    (actual_norm_cutoff_bound 326 actual326_norm_local_summable actual326_norm_euler_product)

end ActualOriginalGlobalSeriesSummable318
