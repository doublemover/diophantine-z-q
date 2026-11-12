module
public import ActualOriginalScaledDisplacementBlockCount318
public section
noncomputable section
namespace ActualOriginalMixedAbelIdentity318
open ActualOriginalFiniteAbel318
open scoped BigOperators

@[expose] def rectangularWeighted (f k : ℕ → ℂ) (g : ℕ → ℕ → ℂ) (N M : ℕ) : ℂ :=
  ∑ i∈Finset.range N, ∑ j∈Finset.range M, g i j*f i*k j
@[expose] def mixedVariation (g : ℕ → ℕ → ℂ) (N M : ℕ) : ℝ :=
  variation (fun i => g i M) N+
    ∑ j∈Finset.range M, variation (fun i => g i j-g i (j+1)) N

/-- First apply Abel in the second axis, then keep the ORIGINAL first-axis
weighted sums. The arbitrary two-variable weight is never factorized. -/
theorem actual_rectangular_abel_identity (f k : ℕ → ℂ) (g : ℕ → ℕ → ℂ) (N M : ℕ) :
    rectangularWeighted f k g (N+1) (M+1)=
      weightedPrefix f (fun i => g i M) (N+1)*prefix k (M+1)+
        ∑ j∈Finset.range M,
          weightedPrefix f (fun i => g i j-g i (j+1)) (N+1)*prefix k (j+1) := by
  calc
    _ = ∑ i∈Finset.range (N+1), weightedPrefix k (g i) (M+1)*f i := by
      unfold rectangularWeighted weightedPrefix
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i∈Finset.range (N+1),
        (g i M*prefix k (M+1)+∑ j∈Finset.range M, (g i j-g i (j+1))*prefix k (j+1))*f i := by
      simp_rw [actual_finite_abel]
    _ = _ := by
      simp only [weightedPrefix,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring

lemma actual_mixed_variation_nonneg (g : ℕ → ℕ → ℂ) (N M : ℕ) :
    0≤mixedVariation g N M :=
  add_nonneg (variation_nonneg _ _) (Finset.sum_nonneg (fun j hj => variation_nonneg _ _))

end ActualOriginalMixedAbelIdentity318
