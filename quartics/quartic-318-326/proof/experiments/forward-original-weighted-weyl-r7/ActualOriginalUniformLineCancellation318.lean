module
public import ActualOriginalBoxSliceAggregation318
public section
noncomputable section
namespace ActualOriginalUniformLineCancellation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalLineCorrelation318 ActualOriginalQuadraticPolarization318
open ActualOriginalScaledLineVariation318 ActualOriginalUniformPairedVariation318
open ActualOriginalSmoothGlobalBounds318 ActualOriginalPairedWeightVariation318
open scoped ContDiff

/-- A scale-uniform cancellation bound on the actual scaled ambient
weight. Constants are produced once from W and work for ALL h,y,v,B,R,N.
The displayed direction norm and finite frequency are not suppressed. -/
theorem actual_smooth_uniform_line_cancellation (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L : ℝ, 0≤A ∧ 0≤L ∧ ∀ B : ℝ, 0<B → ∀ R : ℝ,
      ∀ h y v : Coordinates ℤ, ∀ N : ℕ, (N : ℝ)≤R*B →
      ∀ θ : AddCircle (1 : ℝ), fourier (2*originalBilinear κ h v) θ≠1 →
      ‖originalLineCorrelation κ (latticeWeight B W) h y v (N+1) θ‖≤
        min ((N : ℝ)+1) (2/‖fourier (2*originalBilinear κ h v) θ-1‖)*
          (A^2+2*A*R*L*‖integerEmbed v‖) := by
  obtain ⟨A,L,hA,hL,ha,hl⟩ := actual_smooth_global_bounds W hW hc
  refine ⟨A,L,hA,hL,fun B hB R h y v N hN θ hn => ?_⟩
  have hb := actual_original_line_cancellation κ (latticeWeight B W) h y v N θ hn
  have hv := actual_uniform_paired_variation B hB W A L hA hL ha hl R h y v N hN
  have hp : (fun j => latticeWeight B W (h+linePoint y v j))=
      scaledLineWeight B W (h+y) v := by
    funext j
    rw [actual_translated_line]
    rfl
  rw [hp] at hb
  change ‖originalLineCorrelation κ (latticeWeight B W) h y v (N+1) θ‖≤
    min ((N : ℝ)+1) (2/‖fourier (2*originalBilinear κ h v) θ-1‖)*
      ActualOriginalFiniteAbel318.variation
        (pairedWeight (scaledLineWeight B W (h+y) v) (scaledLineWeight B W y v)) N at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_left hv (le_min (by positivity) (by positivity))

end ActualOriginalUniformLineCancellation318
