module
public import ActualOriginalLocalSeriesConvergence318
public section
noncomputable section
namespace ActualOriginalLocalFourierProduct318
open ActualOriginalCompleteFourierCount318 ActualOriginalLocalSeriesConvergence318
open ActualGeometricLocalSeries318 ActualOriginalAllPrimeFactors318
open ActualOriginalNonarchimedeanProduct318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Exact layers of the ORIGINAL complete-frequency averages.
Identification with unit-frequency sums is a separate theorem, not hidden
inside this definition. -/
@[expose] def originalFourierLayers (κ : ℤ) (p : ℕ) [NeZero p] : ℕ → ℂ
  | 0 => completeAverage κ 1
  | n+1 => completeAverage κ (p^(n+1))-completeAverage κ (p^n)

theorem actual_original_fourier_layer_identity (κ : ℤ) (p : ℕ) [NeZero p]
    (n : ℕ) : originalFourierLayers κ p n = (originalLayers κ p n : ℂ) := by
  cases n with
  | zero =>
    change completeAverage κ (p^0) = ((ActualFullLocalDensityRecurrence318.volume κ p 0 : ℝ) : ℂ)
    rw [actual_prime_power_complete_average]
    norm_cast
  | succ n =>
    change completeAverage κ (p^(n+1))-completeAverage κ (p^n) =
      (((ActualFullLocalDensityRecurrence318.volume κ p (n+1) : ℝ)-
        (ActualFullLocalDensityRecurrence318.volume κ p n : ℝ)) : ℂ)
    rw [actual_prime_power_complete_average,actual_prime_power_complete_average]
    push_cast
    rfl

@[expose] def originalLocalSeries (κ : ℤ) (p : ℕ) : ℝ :=
  if p.Prime then ∑' n, originalLayers κ p n else 1

theorem actual318_local_series_factor (p : ℕ) : originalLocalSeries 318 p = density318 p := by
  by_cases hp : p.Prime
  · rw [originalLocalSeries,if_pos hp]
    exact (actual318_local_layers p hp).2.tsum_eq
  · simp only [originalLocalSeries,density318,if_neg hp]

theorem actual326_local_series_factor (p : ℕ) : originalLocalSeries 326 p = density326 p := by
  by_cases hp : p.Prime
  · rw [originalLocalSeries,if_pos hp]
    exact (actual326_local_layers p hp).2.tsum_eq
  · simp only [originalLocalSeries,density326,if_neg hp]

/-- The product of the ACTUAL absolutely convergent local Fourier-layer
series is the entire positive original local-density product, with all bad
places included. This is not yet the sum of primitive-frequency global
singular-series coefficients over arbitrary denominators. -/
theorem actual_original_local_fourier_products :
    ∃ S318 S326 : ℝ, 0 < S318 ∧ 0 < S326 ∧
      HasProd (originalLocalSeries 318) S318 ∧ HasProd (originalLocalSeries 326) S326 := by
  obtain ⟨S,hS,hpS⟩ := actual_full318_positive_product
  obtain ⟨T,hT,hpT⟩ := actual_full326_positive_product
  have h318 : originalLocalSeries 318 = density318 := funext actual318_local_series_factor
  have h326 : originalLocalSeries 326 = density326 := funext actual326_local_series_factor
  rw [h318,h326]
  exact ⟨S,T,hS,hT,hpS,hpT⟩

end ActualOriginalLocalFourierProduct318
