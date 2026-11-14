module
public import ActualOriginalQuadraticShiftCancellation318
public section
noncomputable section
namespace ActualOriginalFiniteAbel318
open scoped BigOperators

@[expose] def prefix (f : ℕ → ℂ) (N : ℕ) : ℂ := ∑ j ∈ Finset.range N, f j
@[expose] def weightedPrefix (f g : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, g j*f j
@[expose] def variation (g : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖g N‖+∑ j ∈ Finset.range N, ‖g j-g (j+1)‖

lemma prefix_succ (f : ℕ → ℂ) (N : ℕ) : prefix f (N+1)=prefix f N+f N :=
  Finset.sum_range_succ _ _
lemma weightedPrefix_succ (f g : ℕ → ℂ) (N : ℕ) :
    weightedPrefix f g (N+1)=weightedPrefix f g N+g N*f N :=
  Finset.sum_range_succ _ _

/-- Finite Abel summation with the exact terminal term. Arbitrary
complex weights are allowed; no product-weight hypothesis occurs. -/
theorem actual_finite_abel (f g : ℕ → ℂ) (N : ℕ) :
    weightedPrefix f g (N+1)=g N*prefix f (N+1)+
      ∑ j ∈ Finset.range N, (g j-g (j+1))*prefix f (j+1) := by
  induction N with
  | zero => simp [weightedPrefix,prefix]
  | succ N ih =>
    rw [weightedPrefix_succ,ih,Finset.sum_range_succ,prefix_succ f (N+1)]
    ring

lemma variation_nonneg (g : ℕ → ℂ) (N : ℕ) : 0≤variation g N := by
  exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- A bound on every actual initial interval transfers to arbitrary
weights with their literal endpoint-plus-discrete-variation cost. -/
theorem actual_finite_abel_bound (f g : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hprefix : ∀ n≤N+1, ‖prefix f n‖≤M) :
    ‖weightedPrefix f g (N+1)‖≤M*variation g N := by
  rw [actual_finite_abel]
  calc
    _ ≤ ‖g N*prefix f (N+1)‖+
        ‖∑ j ∈ Finset.range N, (g j-g (j+1))*prefix f (j+1)‖ := norm_add_le _ _
    _ ≤ ‖g N‖*‖prefix f (N+1)‖+
        ∑ j ∈ Finset.range N, ‖g j-g (j+1)‖*‖prefix f (j+1)‖ := by
      simpa only [norm_mul] using add_le_add_left
        (norm_sum_le (Finset.range N) (fun j => (g j-g (j+1))*prefix f (j+1)))
        ‖g N*prefix f (N+1)‖
    _ ≤ ‖g N‖*M+∑ j ∈ Finset.range N, ‖g j-g (j+1)‖*M := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hprefix (N+1) le_rfl) (norm_nonneg _)
      · apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hprefix (j+1) (by have := Finset.mem_range.mp hj; omega))
          (norm_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; unfold variation; ring

end ActualOriginalFiniteAbel318
