module
public import ActualOriginalMixedAbelIdentity318
public section
noncomputable section
namespace ActualOriginalMixedAbelBound318
open ActualOriginalFiniteAbel318 ActualOriginalMixedAbelIdentity318
open scoped BigOperators

/-- Two independent prefix cancellations multiply, for a genuinely
arbitrary two-dimensional weight, at its literal mixed variation cost.
This is the needed alternative to taking absolute values after one axis. -/
theorem actual_rectangular_abel_bound (f k : ℕ → ℂ) (g : ℕ → ℕ → ℂ)
    (N M : ℕ) (A B : ℝ)
    (hf : ∀ n≤N+1, ‖prefix f n‖≤A) (hk : ∀ m≤M+1, ‖prefix k m‖≤B) :
    ‖rectangularWeighted f k g (N+1) (M+1)‖≤A*B*mixedVariation g N M := by
  have hA : 0≤A := (norm_nonneg _).trans (hf 0 (by omega))
  have hterm (u : ℕ → ℂ) (m : ℕ) (hm : m≤M+1) :
      ‖weightedPrefix f u (N+1)*prefix k m‖≤A*B*variation u N := by
    rw [norm_mul]
    have hu := actual_finite_abel_bound f u N A hf
    have hh := mul_le_mul hu (hk m hm) (norm_nonneg _) (mul_nonneg hA (variation_nonneg u N))
    nlinarith
  rw [actual_rectangular_abel_identity]
  calc
    _ ≤ ‖weightedPrefix f (fun i => g i M) (N+1)*prefix k (M+1)‖+
        ‖∑ j∈Finset.range M,
          weightedPrefix f (fun i => g i j-g i (j+1)) (N+1)*prefix k (j+1)‖ := norm_add_le _ _
    _ ≤ A*B*variation (fun i => g i M) N+
        ∑ j∈Finset.range M,
          ‖weightedPrefix f (fun i => g i j-g i (j+1)) (N+1)*prefix k (j+1)‖ :=
      add_le_add (hterm _ _ le_rfl) (norm_sum_le _ _)
    _ ≤ A*B*variation (fun i => g i M) N+
        ∑ j∈Finset.range M, A*B*variation (fun i => g i j-g i (j+1)) N := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro j hj
      exact hterm _ _ (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by unfold mixedVariation; rw [mul_add,Finset.mul_sum]; ring

end ActualOriginalMixedAbelBound318
