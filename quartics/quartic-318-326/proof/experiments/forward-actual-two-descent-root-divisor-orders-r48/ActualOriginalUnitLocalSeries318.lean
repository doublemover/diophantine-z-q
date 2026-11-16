module
public import ActualOriginalUnitFourierLayers318
public section
noncomputable section
namespace ActualOriginalUnitLocalSeries318
open ActualOriginalUnitFourierLayers318 ActualOriginalLocalFourierProduct318
open ActualOriginalLocalSeriesConvergence318 ActualOriginalAllPrimeFactors318
open ActualOriginalNonarchimedeanProduct318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_unit_frequency_real (κ : ℤ) (p : ℕ) [NeZero p] (hp : p.Prime) (n : ℕ) :
    unitAverage κ (p^n) = (originalLayers κ p n : ℂ) := by
  rw [actual_unit_frequency_layers κ p hp,actual_original_fourier_layer_identity]

/-- Absolute convergence is transferred only after identifying each
literal unit-frequency coefficient with the actual original count layer. -/
theorem actual318_unit_local_series (p : ℕ) [NeZero p] (hp : p.Prime) :
    Summable (fun n => ‖unitAverage 318 (p^n)‖) ∧
      HasSum (fun n => unitAverage 318 (p^n)) (density318 p : ℂ) := by
  obtain ⟨hn,hs⟩ := actual318_local_layers p hp
  constructor
  · simpa only [actual_unit_frequency_real 318 p hp,Complex.norm_real] using hn
  · simpa only [actual_unit_frequency_real 318 p hp] using Complex.ofRealCLM.hasSum hs

theorem actual326_unit_local_series (p : ℕ) [NeZero p] (hp : p.Prime) :
    Summable (fun n => ‖unitAverage 326 (p^n)‖) ∧
      HasSum (fun n => unitAverage 326 (p^n)) (density326 p : ℂ) := by
  obtain ⟨hn,hs⟩ := actual326_local_layers p hp
  constructor
  · simpa only [actual_unit_frequency_real 326 p hp,Complex.norm_real] using hn
  · simpa only [actual_unit_frequency_real 326 p hp] using Complex.ofRealCLM.hasSum hs

@[expose] def unitLocalSeries (κ : ℤ) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∑' n, unitAverage κ (p^n)).re
  else 1

lemma actual318_unit_factor (p : ℕ) : unitLocalSeries 318 p = density318 p := by
  by_cases hp : p.Prime
  · letI : NeZero p := ⟨hp.ne_zero⟩
    rw [unitLocalSeries,dif_pos hp,(actual318_unit_local_series p hp).2.tsum_eq]
    exact Complex.ofReal_re _
  · simp only [unitLocalSeries,dif_neg hp,density318,if_neg hp]

lemma actual326_unit_factor (p : ℕ) : unitLocalSeries 326 p = density326 p := by
  by_cases hp : p.Prime
  · letI : NeZero p := ⟨hp.ne_zero⟩
    rw [unitLocalSeries,dif_pos hp,(actual326_unit_local_series p hp).2.tsum_eq]
    exact Complex.ofReal_re _
  · simp only [unitLocalSeries,dif_neg hp,density326,if_neg hp]

/-- The Euler factors now are the actual absolutely convergent
unit-frequency series, at EVERY prime. Identification with a single global
sum over all positive denominators still requires its own convergence and
multiplicativity argument. Primitive-point scaling remains separate. -/
theorem actual_original_unit_local_products :
    ∃ S318 S326 : ℝ, 0 < S318 ∧ 0 < S326 ∧
      HasProd (unitLocalSeries 318) S318 ∧ HasProd (unitLocalSeries 326) S326 := by
  obtain ⟨S,hS,hpS⟩ := actual_full318_positive_product
  obtain ⟨T,hT,hpT⟩ := actual_full326_positive_product
  have h318 : unitLocalSeries 318 = density318 := funext actual318_unit_factor
  have h326 : unitLocalSeries 326 = density326 := funext actual326_unit_factor
  rw [h318,h326]
  exact ⟨S,T,hS,hT,hpS,hpT⟩

end ActualOriginalUnitLocalSeries318
