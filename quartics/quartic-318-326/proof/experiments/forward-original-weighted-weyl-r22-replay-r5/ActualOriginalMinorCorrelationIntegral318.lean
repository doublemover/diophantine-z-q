module
public import ActualOriginalIntervalSliceIdentity318
public section
noncomputable section
namespace ActualOriginalMinorCorrelationIntegral318
open QuadricCRTAssembly318 ActualOriginalMajorArcDomain318
open ActualOriginalCircleMinorArcIdentity318 ActualOriginalScaledCircle318
open ActualOriginalCompactCircleCount318 ActualOriginalWeightedWeylIdentity318
open ActualOriginalWeightedWeylBound318 MeasureTheory
open scoped BigOperators

/-- An explicit bound for the ACTUAL minor integral from an actual
correlation budget. The missing power-saving budget is an explicit input,
not a new definition of the minor remainder or an assumed decay limit. -/
theorem actual_minor_integral_of_correlation_budget (κ : ℤ) (N : ℕ) (B : ℝ)
    (W : Coordinates ℝ → ℝ) (s : Finset (Coordinates ℤ))
    (hs : ∀ x∉s, latticeWeight B W x=0) (C : ℝ) (hC : 0≤C)
    (hbudget : ∀ θ∈minorDomain N B,
      (∑ h ∈ differences s, ‖linearCorrelation κ s (latticeWeight B W)
        (θ : AddCircle (1 : ℝ)) h‖)≤C^2) :
    ‖minorArcIntegral κ N B W‖≤C*volume.real (minorDomain N B) := by
  have hfin : volume (minorDomain N B)<⊤ := by
    apply lt_of_le_of_lt (measure_mono Set.diff_subset)
    exact measure_Ioc_lt_top
  apply norm_setIntegral_le_of_norm_le_const hfin
  intro θ hθ
  have hb := (actual_original_weyl_square_bound κ s (latticeWeight B W)
    (θ : AddCircle (1 : ℝ))).trans (hbudget θ hθ)
  rw [actual_circle_eq_finite κ B W s hs]
  nlinarith [norm_nonneg (ActualOriginalFiniteCircleIdentity318.originalCircleSum κ s (latticeWeight B W)
    (θ : AddCircle (1 : ℝ)))]

end ActualOriginalMinorCorrelationIntegral318
