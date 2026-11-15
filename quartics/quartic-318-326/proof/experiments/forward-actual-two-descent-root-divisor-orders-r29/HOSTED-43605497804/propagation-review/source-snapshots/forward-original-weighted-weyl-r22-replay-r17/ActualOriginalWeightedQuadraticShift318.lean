module
public import ActualOriginalPairedWeightVariation318
public section
noncomputable section
namespace ActualOriginalWeightedQuadraticShift318
open ActualOriginalWeightedLinearCancellation318 ActualOriginalFiniteAbel318
open ActualOriginalPairedWeightVariation318 ActualOriginalQuadraticShiftCancellation318
open scoped BigOperators

/-- Actual two weights at the two ends of a quadratic displacement. -/
@[expose] def weightedQuadraticShift (c h m : ℤ) (u v : ℕ → ℂ)
    (N : ℕ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range N, pairedWeight u v j*
    (fourier (c*(m+(j : ℤ)+h)^2) θ*
      starRingEnd ℂ (fourier (c*(m+(j : ℤ))^2) θ))

lemma actual_weighted_shift_linear (c h m : ℤ) (u v : ℕ → ℂ)
    (N : ℕ) (θ : AddCircle (1 : ℝ)) :
    weightedQuadraticShift c h m u v N θ=
      fourier (c*h^2) θ*weightedLinearInterval (2*c*h) m (pairedWeight u v) N θ := by
  simp only [weightedQuadraticShift,actual_quadratic_shift_phase,weightedLinearInterval,
    weightedPrefix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The finite shift estimate genuinely includes nonconstant paired
weights. The cost is their actual variation, not an assumed product cut-off. -/
theorem actual_weighted_shift_cancellation (c h m : ℤ) (u v : ℕ → ℂ)
    (N : ℕ) (θ : AddCircle (1 : ℝ)) (hn : fourier (2*c*h) θ≠1) :
    ‖weightedQuadraticShift c h m u v (N+1) θ‖≤
      min ((N : ℝ)+1) (2/‖fourier (2*c*h) θ-1‖)*variation (pairedWeight u v) N := by
  rw [actual_weighted_shift_linear,norm_mul]
  have he : ‖fourier (c*h^2) θ‖=1 := Circle.norm_coe _
  rw [he,one_mul]
  exact actual_weighted_linear_cancellation (2*c*h) m (pairedWeight u v) N θ hn

end ActualOriginalWeightedQuadraticShift318
