module
public import ActualOriginalZeroModeScaling318
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public section
noncomputable section
namespace ActualOriginalZeroModeLimit318
open QuadricCRTAssembly318 ActualOriginalCoordinateFrequency318
open ActualOriginalGlobalCoefficient318 ActualOriginalGlobalSingularSeries318
open ActualOriginalAllPrimeFactors318
open ActualOriginalAmbientFourierIdentity318 ActualOriginalPositiveSingularIntegral318
open ActualOriginalUndampedSingularIntegral318 ActualOriginalRealGoodRegion318
open ActualOriginalPositiveGraphIntegral318 MeasureTheory Filter
open scoped BigOperators ContDiff
set_option maxHeartbeats 16000000

/-- Normalized finite-denominator, finite-frequency ZERO-MODE main
term. The coefficients and positive singular integral have already been
identified with the actual rational-arc summand in the preceding modules. -/
@[expose] def normalizedZeroMode (κ : ℤ) (W : Coordinates ℝ → ℝ) (N : ℕ) (T : ℝ) : ℂ :=
  (∑ q ∈ Finset.range N, coefficient κ q) *
    ∫ β : ℝ in -T..T, originalCoordinateFourier (κ : ℝ) β W 0

/-- Independent denominator and frequency cutoffs may tend to infinity
at any rates. Absolute series convergence and original integral convergence
are established before taking this product limit. -/
theorem actual_zero_mode_limit (κ : ℤ) (W : Coordinates ℝ → ℝ) (S : ℂ)
    (hseries : HasSum (coefficient κ) S)
    (hi : Integrable (originalOscillation (κ : ℝ) W))
    (hmass : (∫ t : ℝ, originalOscillation (κ : ℝ) W t) = 1)
    (Q : ℕ → ℕ) (T : ℕ → ℝ) (hQ : Tendsto Q atTop atTop) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => normalizedZeroMode κ W (Q n) (T n)) atTop (𝓝 S) := by
  have hs := hseries.tendsto_sum_nat.comp hQ
  have ht := actual_positive_zero_cutoff (κ : ℝ) W hi T hT
  rw [hmass] at ht
  simpa only [normalizedZeroMode,mul_one] using hs.mul ht

/-- One same original nonnegative smooth compact weight retains all
original prime-form support and graph-mass conditions, and its normalized
zero mode tends to the actual positive full singular series. This does not
assert that the nonzero modes or minor arcs are negligible. -/
@[expose] def NormalizedZeroModeInput {J : Type*} [Fintype J]
    (κ : ℤ) (γ : J → ℝ) (S : ℝ) : Prop :=
  ∃ (x : Coordinates ℝ) (W : Coordinates ℝ → ℝ) (η : ℝ),
    equation (κ : ℝ) x = 0 ∧ 0 < x.1.1 ∧ 0 < η ∧ HasCompactSupport W ∧
    ContDiff ℝ ∞ W ∧ (∀ y, 0 ≤ W y) ∧ 0 < W x ∧
    (∀ y ∈ tsupport W, y ∈ region γ ∧ η < ActualQuadricTaylor318.gradient (κ : ℝ) y 0) ∧
    graphMass (κ : ℝ) W = 1 ∧ Integrable (originalOscillation (κ : ℝ) W) ∧
    ∀ (Q : ℕ → ℕ) (T : ℕ → ℝ), Tendsto Q atTop atTop → Tendsto T atTop atTop →
      Tendsto (fun n => normalizedZeroMode κ W (Q n) (T n)) atTop (𝓝 (S : ℂ))

lemma actual_normalized_zero_mode_input {J : Type*} [Fintype J]
    (κ : ℤ) (hκ : 0 < (κ : ℝ)) (γ : J → ℝ) (S : ℝ)
    (hseries : HasSum (coefficient κ) (S : ℂ)) : NormalizedZeroModeInput κ γ S := by
  obtain ⟨x,W,η,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hi,hint⟩ :=
    actual_original_normalized_undamped_input (κ : ℝ) hκ γ
  refine ⟨x,W,η,hx,hpos,hη,hWc,hW,hWn,hWx,hsupport,hmass,hi,?_⟩
  intro Q T hQ hT
  exact actual_zero_mode_limit κ W (S : ℂ) hseries hi hint Q T hQ hT

theorem actual318_positive_zero_mode_input {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0 < S ∧ HasProd density318 S ∧ NormalizedZeroModeInput 318 γ S := by
  obtain ⟨S,hS,hs,hprod⟩ := actual318_global_singular_series
  exact ⟨S,hS,hprod,actual_normalized_zero_mode_input 318 (by norm_num) γ S hs⟩

theorem actual326_positive_zero_mode_input {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ S : ℝ, 0 < S ∧ HasProd density326 S ∧ NormalizedZeroModeInput 326 γ S := by
  obtain ⟨S,hS,hs,hprod⟩ := actual326_global_singular_series
  exact ⟨S,hS,hprod,actual_normalized_zero_mode_input 326 (by norm_num) γ S hs⟩

end ActualOriginalZeroModeLimit318
