module
public import ActualOriginalWeightedLinearCancellation318
public section
noncomputable section
namespace ActualOriginalPairedWeightVariation318
open ActualOriginalFiniteAbel318
open scoped BigOperators

@[expose] def pairedWeight (u v : ℕ → ℂ) (j : ℕ) : ℂ := u j*starRingEnd ℂ (v j)
@[expose] def incrementVariation (u : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, ‖u j-u (j+1)‖

/-- Both actual weights contribute to variation. Dropping the variation
of the translated factor would not be a valid weighted Weyl estimate. -/
lemma actual_paired_weight_increment (u v : ℕ → ℂ) (j : ℕ) :
    ‖pairedWeight u v j-pairedWeight u v (j+1)‖≤
      ‖u j‖*‖v j-v (j+1)‖+‖u j-u (j+1)‖*‖v (j+1)‖ := by
  have he : pairedWeight u v j-pairedWeight u v (j+1)=
      u j*starRingEnd ℂ (v j-v (j+1))+
        (u j-u (j+1))*starRingEnd ℂ (v (j+1)) := by
    simp only [pairedWeight,map_sub]
    ring
  rw [he]
  simpa only [norm_mul,norm_star] using
    norm_add_le (u j*starRingEnd ℂ (v j-v (j+1)))
      ((u j-u (j+1))*starRingEnd ℂ (v (j+1)))

/-- A concrete bound in the actual two slice weights. A bounds u and
B bounds v on the entire closed index range including the endpoint. -/
theorem actual_paired_weight_variation (u v : ℕ → ℂ) (N : ℕ) (A B : ℝ)
    (hu : ∀ j≤N, ‖u j‖≤A) (hv : ∀ j≤N, ‖v j‖≤B) :
    variation (pairedWeight u v) N≤
      A*B+A*incrementVariation v N+B*incrementVariation u N := by
  have hA : 0≤A := (norm_nonneg (u 0)).trans (hu 0 (Nat.zero_le _))
  have hend : ‖pairedWeight u v N‖≤A*B := by
    simpa only [pairedWeight,norm_mul,norm_star] using
      mul_le_mul (hu N le_rfl) (hv N le_rfl) (norm_nonneg _) hA
  have hs : (∑ j ∈ Finset.range N, ‖pairedWeight u v j-pairedWeight u v (j+1)‖)≤
      ∑ j ∈ Finset.range N, (A*‖v j-v (j+1)‖+B*‖u j-u (j+1)‖) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j+1≤N := by have := Finset.mem_range.mp hj; omega
    apply (actual_paired_weight_increment u v j).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hu j (by omega)) (norm_nonneg _)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hv (j+1) hjN) (norm_nonneg (u j-u (j+1)))
  unfold variation
  calc
    _ ≤ A*B+∑ j ∈ Finset.range N, (A*‖v j-v (j+1)‖+B*‖u j-u (j+1)‖) := add_le_add hend hs
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,incrementVariation]; ring

end ActualOriginalPairedWeightVariation318
