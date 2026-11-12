module
public import ActualGoodPrimeProductNormalization318
public section
noncomputable section
namespace ActualOriginalLocalProductBounds318
open scoped BigOperators Topology
open Filter ActualGoodPrimeDensityProduct318 ActualPrimitiveCorrectionProducts318
set_option maxHeartbeats 24000000

@[expose] def partialProduct (f : ℕ → ℝ) (N : ℕ) : ℝ := ∏p∈Finset.range N,f p
lemma partial_pos (f : ℕ → ℝ) (hf : ∀p,0<f p) (N : ℕ) : 0<partialProduct f N :=
  Finset.prod_pos (fun p _ => hf p)

/-- Both lower and upper bounds include EVERY initial cutoff. The
finite prefix is controlled by its actual values and reciprocal values,
not thrown away by an eventual-convergence argument. -/
theorem all_cutoff_bounds (f : ℕ → ℝ) (hf : ∀p,0<f p) (C : ℝ) (hC : 0<C)
    (hprod : HasProd f C) :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct f N ∧ partialProduct f N≤U := by
  have ht : Tendsto (partialProduct f) atTop (𝓝 C) := hprod.tendsto_prod_nat
  have he : ∀ᶠ N : ℕ in atTop,C/2<partialProduct f N ∧ partialProduct f N<C+1 :=
    (ht.eventually (Ioi_mem_nhds (by linarith))).and
      (ht.eventually (Iio_mem_nhds (by linarith)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  let A : ℝ := 1+∑n∈Finset.range N₀,1/partialProduct f n
  let B : ℝ := ∑n∈Finset.range N₀,partialProduct f n
  have hA : 0<A := by
    have hh : 0≤∑n∈Finset.range N₀,1/partialProduct f n :=
      Finset.sum_nonneg (fun n _ => le_of_lt (one_div_pos.mpr (partial_pos f hf n)))
    dsimp [A]
    linarith
  have hB : 0≤B := Finset.sum_nonneg (fun n _ => (partial_pos f hf n).le)
  refine ⟨min (C/2) (1/A),C+1+B,lt_min (by linarith) (one_div_pos.mpr hA),by linarith,?_⟩
  intro N
  by_cases hn : N₀≤N
  · have hh := hN₀ N hn
    exact ⟨le_trans (min_le_left _ _) hh.1.le,by linarith [hh.2]⟩
  · have hm : N∈Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hp := partial_pos f hf N
    have hrec : 1/partialProduct f N≤A := by
      have hh := Finset.single_le_sum
        (fun n _ => le_of_lt (one_div_pos.mpr (partial_pos f hf n))) hm
      dsimp [A]
      linarith [hh]
    have hlo : 1/A≤partialProduct f N := by
      apply (div_le_iff₀ hA).mpr
      have hh := (div_le_iff₀ hp).mp hrec
      nlinarith [hh]
    have hhi : partialProduct f N≤B := Finset.single_le_sum
      (fun n _ => (partial_pos f hf n).le) hm
    exact ⟨le_trans (min_le_right _ _) hlo,by linarith⟩

/-- Actual unrestricted original good-prime cutoff products are
uniformly bounded above and AWAY FROM ZERO at every cutoff. -/
theorem actual_good_prime_all_cutoffs (κ : ℤ) :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct (factor κ) N ∧ partialProduct (factor κ) N≤U := by
  obtain ⟨C,hC,hprod⟩ := actual_good_prime_positive_product κ
  exact all_cutoff_bounds _ (factor_pos κ) C hC hprod

/-- The same all-cutoff control is produced for BOTH the primitive
factor and the exact singular correction, on the identical prime set. -/
theorem actual_primitive_all_cutoffs (κ : ℤ) (s : ℕ) (hs : 2≤s) :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct (inversePowerFactor κ s) N ∧
      partialProduct (inversePowerFactor κ s) N≤U := by
  obtain ⟨C,hC,hprod⟩ := actual_inverse_power_positive_product κ s hs
  exact all_cutoff_bounds _ (fun p => inversePowerFactor_pos κ s p (by omega)) C hC hprod

end ActualOriginalLocalProductBounds318
