module
public import ActualGaussianSourcePartition318
public section
noncomputable section
namespace ActualGaussianTwoChartTail318
open scoped BigOperators
open ActualGaussianSourcePartition318 OriginalGlobalBadMass318 OriginalUniformEulerRankin318
open OriginalBadSliceLogWeight318
set_option maxHeartbeats 12000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def goodTotal (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ :=
  ∑ t∈labels B, goodMass B κ t side T Y γ
@[expose] def sourceTotal (B : ℕ) (κ : ℤ) (side : Bool) (Y : ℕ) (γ : J → ℤ) : ℝ :=
  ∑ t∈labels B, sourceMass B κ t side Y γ
@[expose] def goodBudget (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) : ℝ :=
  if side then ActualQuarticLabelHeight318.labelBudget κ B (6*(B:ℝ)) T Y
  else ActualFirstChartLabelTail318.labelBudget κ B (6*(B:ℝ)) T Y

lemma source_total_partition (B : ℕ) (κ : ℤ) (side : Bool)
    (T : ℝ) (Y : ℕ) (γ : J → ℤ) :
    sourceTotal B κ side Y γ≤goodTotal B κ side T Y γ+
      OriginalGlobalBadMass318.totalMass B κ side T γ := by
  have hh := Finset.sum_le_sum (fun t (_ : t∈labels B) =>
    original_weighted_partition B κ t side T Y γ)
  simpa only [sourceTotal,goodTotal,OriginalGlobalBadMass318.totalMass,Finset.sum_add_distrib] using hh

lemma actual_good_chart_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0) (side : Bool)
    (T : ℝ) (hT : 0≤T) (hTB : T≤6*(B:ℝ)) (Y : ℕ) (hY : 3≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    goodTotal B κ side T Y γ*Real.log (Y:ℝ)≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*goodBudget B κ side T Y*weightCeiling B γ := by
  cases side
  · exact ActualFirstGaussianGoodSlice318.actual_original_weighted_good_tail
      B hB κ hκ T hT hTB Y hY γ δ hδ
  · exact ActualGaussianWeightedGoodTail318.actual_original_weighted_good_tail
      B hB κ hκ T hT hTB Y hY γ δ hδ

/-- The good/bad split is now consumed on ACTUAL original source points.
No good-lattice or supplied source cover remains among the hypotheses.
The true Pprime/K second chart and the genuinely valid first P/D chart
are kept separate until their actual weighted masses are joined here. -/
theorem actual_chart_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0) (side : Bool)
    (T : ℝ) (hT : 0<T) (hTB : T≤6*(B:ℝ)) (Y : ℕ) (hY : 3≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    sourceTotal B κ side Y γ*Real.log (Y:ℝ)*T^3≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*goodBudget B κ side T Y*weightCeiling B γ*T^3+
      tailConstant δ*(B:ℝ)^((5:ℝ)+δ)*weightCeiling B γ*Real.log (Y:ℝ) := by
  have hl := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have ht3 := pow_nonneg hT.le 3
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (source_total_partition B κ side T Y γ) hl) ht3
  have hg := mul_le_mul_of_nonneg_right
    (actual_good_chart_tail B hB κ hκ side T hT.le hTB Y hY γ δ hδ) ht3
  have hb := mul_le_mul_of_nonneg_right
    (power_weighted_tail B hB κ side T hT γ δ hδ) hl
  nlinarith only [hp,hg,hb]

/-- Total of the two original nonzero-label chart contributions. Overlap
is counted, not incorrectly deduplicated; this gives a safe global source
upper bound once the separate zero/both-label strata are supplied. -/
@[expose] def twoChartMass (B : ℕ) (κ : ℤ) (Y : ℕ) (γ : J → ℤ) : ℝ :=
  sourceTotal B κ false Y γ+sourceTotal B κ true Y γ

theorem actual_two_chart_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (T : ℝ) (hT : 0<T) (hTB : T≤6*(B:ℝ)) (Y : ℕ) (hY : 3≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    twoChartMass B κ Y γ*Real.log (Y:ℝ)*T^3≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*
        (goodBudget B κ false T Y+goodBudget B κ true T Y)*weightCeiling B γ*T^3+
      2*tailConstant δ*(B:ℝ)^((5:ℝ)+δ)*weightCeiling B γ*Real.log (Y:ℝ) := by
  have hf := actual_chart_tail B hB κ hκ false T hT hTB Y hY γ δ hδ
  have ht := actual_chart_tail B hB κ hκ true T hT hTB Y hY γ δ hδ
  dsimp [twoChartMass]
  nlinarith only [hf,ht]

end ActualGaussianTwoChartTail318
