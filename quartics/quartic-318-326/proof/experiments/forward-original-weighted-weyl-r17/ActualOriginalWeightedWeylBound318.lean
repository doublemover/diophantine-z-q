module
public import ActualOriginalWeightedWeylIdentity318
public section
noncomputable section
namespace ActualOriginalWeightedWeylBound318
open QuadricCRTAssembly318 ActualOriginalWeightedWeylIdentity318
open ActualOriginalFiniteCircleIdentity318 ActualOriginalCompactCircleCount318
open ActualOriginalScaledCircle318
open scoped BigOperators

/-- A genuine Weyl square bound by absolute LINEAR correlations, with
the original paired weights and the complete actual displacement set. -/
theorem actual_original_weyl_square_bound (κ : ℤ) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) (θ : AddCircle (1 : ℝ)) :
    ‖originalCircleSum κ s w θ‖^2 ≤
      ∑ h ∈ differences s, ‖linearCorrelation κ s w θ h‖ := by
  classical
  calc
    _ = ‖originalCircleSum κ s w θ*starRingEnd ℂ (originalCircleSum κ s w θ)‖ := by
      simp [norm_mul,pow_two]
    _ = ‖∑ h ∈ differences s, fourier (equation κ h) θ*linearCorrelation κ s w θ h‖ := by
      rw [actual_original_weighted_weyl]
    _ ≤ ∑ h ∈ differences s, ‖fourier (equation κ h) θ*linearCorrelation κ s w θ h‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [norm_mul]
      have hu : ‖fourier (equation κ h) θ‖ = 1 := Circle.norm_coe _
      rw [hu,one_mul]

/-- The exact compactly supported sum consumed by the existing minor
integral has a finite Weyl bound. The finite set is produced from the
literal scaled weight, rather than supplied as a substitute count. -/
theorem actual_scaled_circle_weyl_bound (κ : ℤ) (B : ℝ) (hB : B ≠ 0)
    (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    ∃ s : Finset (Coordinates ℤ), ∀ θ : ℝ,
      ‖scaledCircleSum κ θ B W‖^2 ≤
        ∑ h ∈ differences s,
          ‖linearCorrelation κ s (latticeWeight B W) (θ : AddCircle (1 : ℝ)) h‖ := by
  obtain ⟨s,hs⟩ := actual_weight_finite_support B hB W hW
  refine ⟨s,fun θ => ?_⟩
  rw [actual_circle_eq_finite κ B W s hs]
  exact actual_original_weyl_square_bound κ s (latticeWeight B W) (θ : AddCircle (1 : ℝ))

end ActualOriginalWeightedWeylBound318
