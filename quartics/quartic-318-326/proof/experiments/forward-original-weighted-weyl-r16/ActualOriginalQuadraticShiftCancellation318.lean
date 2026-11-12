module
public import ActualOriginalLinearIntervalCancellation318
public section
noncomputable section
namespace ActualOriginalQuadraticShiftCancellation318
open ActualOriginalLinearIntervalCancellation318
open scoped BigOperators

/-- Literal paired quadratic phases at points y+h and y, for every
integer shift and every finite interval. No periodic wraparound. -/
@[expose] def quadraticShiftCorrelation (c h m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range N,
    fourier (c*(m+(j : ℤ)+h)^2) θ*
      starRingEnd ℂ (fourier (c*(m+(j : ℤ))^2) θ)

lemma actual_quadratic_shift_phase (c h y : ℤ) (θ : AddCircle (1 : ℝ)) :
    fourier (c*(y+h)^2) θ*starRingEnd ℂ (fourier (c*y^2) θ) =
      fourier (c*h^2) θ*fourier ((2*c*h)*y) θ := by
  rw [←fourier_neg,←fourier_add,←fourier_add]
  congr 1
  ring

/-- The shift correlation is a unit phase times the actual linear
interval sum at the produced frequency 2*c*h. -/
theorem actual_quadratic_shift_linear (c h m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    quadraticShiftCorrelation c h m N θ =
      fourier (c*h^2) θ*linearIntervalSum (2*c*h) m N θ := by
  simp only [quadraticShiftCorrelation,actual_quadratic_shift_phase,
    linearIntervalSum,Finset.mul_sum]

/-- Actual one-dimensional differenced quadratic cancellation, usable
for each diagonal coefficient 1,1,-1,-1,-kappa of the original quadric.
The frequency and resonance restriction are not replaced by coprimality. -/
theorem actual_quadratic_shift_cancellation (c h m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) (hn : fourier (2*c*h) θ ≠ 1) :
    ‖quadraticShiftCorrelation c h m N θ‖ ≤
      min (N : ℝ) (2/‖fourier (2*c*h) θ-1‖) := by
  rw [actual_quadratic_shift_linear,norm_mul]
  have hu : ‖fourier (c*h^2) θ‖ = 1 := Circle.norm_coe _
  rw [hu,one_mul]
  exact actual_linear_interval_cancellation (2*c*h) m N θ hn

theorem actual_quadratic_shift_length_bound (c h m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    ‖quadraticShiftCorrelation c h m N θ‖ ≤ (N : ℝ) := by
  rw [actual_quadratic_shift_linear,norm_mul]
  have hu : ‖fourier (c*h^2) θ‖ = 1 := Circle.norm_coe _
  rw [hu,one_mul]
  exact actual_linear_interval_length_bound (2*c*h) m N θ

end ActualOriginalQuadraticShiftCancellation318
