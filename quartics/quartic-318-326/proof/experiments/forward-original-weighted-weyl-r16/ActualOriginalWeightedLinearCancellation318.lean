module
public import ActualOriginalFiniteAbel318
public section
noncomputable section
namespace ActualOriginalWeightedLinearCancellation318
open ActualOriginalFiniteAbel318 ActualOriginalLinearIntervalCancellation318
open scoped BigOperators

@[expose] def weightedLinearInterval (c m : ℤ) (g : ℕ → ℂ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  weightedPrefix (fun j => fourier (c*(m+(j : ℤ))) θ) g N

/-- The unweighted cancellation bound now transfers to a genuinely
arbitrary complex weight, at an explicit discrete-variation cost. -/
theorem actual_weighted_linear_cancellation (c m : ℤ) (g : ℕ → ℂ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) (hn : fourier c θ ≠ 1) :
    ‖weightedLinearInterval c m g (N+1) θ‖ ≤
      min ((N : ℝ)+1) (2/‖fourier c θ-1‖)*variation g N := by
  apply actual_finite_abel_bound
  intro n hnN
  change ‖linearIntervalSum c m n θ‖≤_
  have hb := actual_linear_interval_cancellation c m n θ hn
  apply hb.trans
  apply min_le_min
  · exact_mod_cast hnN
  · exact le_rfl

/-- Resonance needs no separate assumption for the universal weighted
length estimate. The zero-length weighted sum is separately exactly zero. -/
theorem actual_weighted_linear_length_bound (c m : ℤ) (g : ℕ → ℂ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    ‖weightedLinearInterval c m g (N+1) θ‖≤((N : ℝ)+1)*variation g N := by
  apply actual_finite_abel_bound
  intro n hn
  exact (actual_linear_interval_length_bound c m n θ).trans (by exact_mod_cast hn)

lemma actual_weighted_linear_empty (c m : ℤ) (g : ℕ → ℂ)
    (θ : AddCircle (1 : ℝ)) : weightedLinearInterval c m g 0 θ=0 := by
  simp [weightedLinearInterval,weightedPrefix]

end ActualOriginalWeightedLinearCancellation318
