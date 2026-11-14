module
public import ActualOriginalScaledLineVariation318
public section
noncomputable section
namespace ActualOriginalUniformPairedVariation318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalLineCorrelation318
open ActualOriginalScaledLineVariation318 ActualOriginalPairedWeightVariation318
open ActualOriginalFiniteAbel318 ActualOriginalSmoothGlobalBounds318
open scoped ContDiff

lemma actual_translated_line (h y v : Coordinates ℤ) (j : ℕ) :
    h+linePoint y v j=linePoint (h+y) v j := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
    dsimp [linePoint] <;> ring

/-- BOTH endpoints of the actual weighted displacement share the same
scale-uniform variation budget, independently of h and y. -/
theorem actual_uniform_paired_variation (B : ℝ) (hB : 0<B)
    (W : Coordinates ℝ → ℝ) (A L : ℝ) (hA : 0≤A) (hL : 0≤L)
    (ha : ∀ x, ‖W x‖≤A) (hl : ∀ x y, ‖W x-W y‖≤L*‖x-y‖)
    (R : ℝ) (h y v : Coordinates ℤ) (N : ℕ) (hN : (N : ℝ)≤R*B) :
    variation (pairedWeight (scaledLineWeight B W (h+y) v)
      (scaledLineWeight B W y v)) N≤A^2+2*A*R*L*‖integerEmbed v‖ := by
  have hp := actual_paired_weight_variation (scaledLineWeight B W (h+y) v)
    (scaledLineWeight B W y v) N A A
    (fun j _ => actual_scaled_line_amplitude B W A ha (h+y) v j)
    (fun j _ => actual_scaled_line_amplitude B W A ha y v j)
  have hu := actual_scaled_line_variation B hB W L hL hl R (h+y) v N hN
  have hv := actual_scaled_line_variation B hB W L hL hl R y v N hN
  have hu' := mul_le_mul_of_nonneg_left hu hA
  have hv' := mul_le_mul_of_nonneg_left hv hA
  nlinarith only [hp,hu',hv']

/-- The constants are PRODUCED from the actual smooth compact W before
any scale, line or displacement is selected. -/
theorem actual_smooth_uniform_paired_constants (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L : ℝ, 0≤A ∧ 0≤L ∧ ∀ B : ℝ, 0<B → ∀ R : ℝ,
      ∀ h y v : Coordinates ℤ, ∀ N : ℕ, (N : ℝ)≤R*B →
      variation (pairedWeight (scaledLineWeight B W (h+y) v)
        (scaledLineWeight B W y v)) N≤A^2+2*A*R*L*‖integerEmbed v‖ := by
  obtain ⟨A,L,hA,hL,ha,hl⟩ := actual_smooth_global_bounds W hW hc
  exact ⟨A,L,hA,hL,fun B hB R h y v N hN =>
    actual_uniform_paired_variation B hB W A L hA hL ha hl R h y v N hN⟩

end ActualOriginalUniformPairedVariation318
