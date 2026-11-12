module
public import ActualGaussianLogBudget318
public import OriginalGlobalBadSource318
public section
noncomputable section
namespace ActualGaussianThresholdTail318
open ActualGaussianSourcePartition318 ActualGaussianTwoChartTail318 ActualGaussianLogBudget318
open OriginalUniformEulerRankin318 OriginalGlobalBadMass318 OriginalBadSliceLogWeight318
set_option maxHeartbeats 12000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def threshold (B : ℕ) : ℝ := (B:ℝ)^((3:ℝ)/4)
lemma threshold_pos (B : ℕ) (hB : 1≤B) : 0<threshold B :=
  Real.rpow_pos_of_pos (by exact_mod_cast (show 0<B by omega)) _
lemma threshold_le_radius (B : ℕ) (hB : 1≤B) : threshold B≤6*(B:ℝ) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hh := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (3:ℝ)/4≤1)
  rw [Real.rpow_one] at hh
  change (B:ℝ)^((3:ℝ)/4)≤_
  linarith

lemma bad_at_threshold (B : ℕ) (hB : 1≤B) (κ : ℤ) (side : Bool)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    OriginalGlobalBadMass318.totalMass B κ side (threshold B) γ≤
      tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*weightCeiling B γ := by
  rw [←OriginalGlobalBadSource318.source_mass_eq]
  exact OriginalGlobalBadSource318.actual_three_quarter_tail B hB κ side γ δ hδ

/-- Threshold is now constructed rather than a user input: T=B^(3/4).
The actual good/bad original-source partition and BOTH genuine chart
routes give the expected11/4 bad exponent, with original log weights. -/
theorem actual_threshold_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 3≤Y) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    twoChartMass B κ Y γ*Real.log (Y:ℝ)≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*combinedBudget κ B (threshold B) Y*weightCeiling B γ+
      2*tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*weightCeiling B γ*Real.log (Y:ℝ) := by
  have hl := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hT := threshold_pos B hB
  have hTB := threshold_le_radius B hB
  have hW := weightCeiling_nonneg B hB γ
  have hC : 0≤2*rankinConstant κ δ*(2*(B:ℝ))^δ := by
    have hh := OriginalUniformEulerRankin318.rankinConstant_pos κ δ hδ
    positivity
  have hf := source_total_partition B κ false (threshold B) Y γ
  have ht := source_total_partition B κ true (threshold B) Y γ
  have hsum := mul_le_mul_of_nonneg_right (add_le_add hf ht) hl
  have hgf := actual_good_chart_tail B hB κ hκ false (threshold B) hT.le hTB Y hY γ δ hδ
  have hgt := actual_good_chart_tail B hB κ hκ true (threshold B) hT.le hTB Y hY γ δ hδ
  have hbf := mul_le_mul_of_nonneg_right (bad_at_threshold B hB κ false γ δ hδ) hl
  have hbt := mul_le_mul_of_nonneg_right (bad_at_threshold B hB κ true γ δ hδ) hl
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_combined_budget κ B hB (threshold B) hT.le Y) hC) hW
  dsimp [twoChartMass]
  nlinarith only [hsum,hgf,hgt,hbf,hbt,hb]

end ActualGaussianThresholdTail318
