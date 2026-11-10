module
public import ActualGaussianHeightGrowth318
public section
noncomputable section
namespace ActualGaussianLogBudget318
open ActualGaussianHeightGrowth318 ActualGaussianTwoChartTail318
set_option maxHeartbeats 10000000

@[expose] def logEnvelope (κ : ℤ) (B : ℕ) : ℝ :=
  Real.log (heightConstant κ)+74*Real.log (B:ℝ)
lemma logEnvelope_nonneg (κ : ℤ) (B : ℕ) (hB : 1≤B) : 0≤logEnvelope κ B := by
  have hc := Real.log_nonneg (heightConstant_one κ)
  have hb := Real.log_nonneg (show (1:ℝ)≤B by exact_mod_cast hB)
  dsimp [logEnvelope]
  positivity

/-- The true polynomial height is consumed as a LOGARITHMIC bound with a
constant independent of B; no huge polynomial factor enters the count. -/
lemma actual_log_heights (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    Real.log (ActualFirstChartLabelTail318.labelHeight κ B (6*(B:ℝ)))≤logEnvelope κ B ∧
    Real.log (ActualQuarticLabelHeight318.labelHeight κ B (6*(B:ℝ)))≤logEnvelope κ B := by
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hc : 0<heightConstant κ := zero_lt_one.trans_le (heightConstant_one κ)
  obtain ⟨hf,hs⟩ := both_heights_growth κ B hB
  have he : Real.log (heightConstant κ*(B:ℝ)^74)=logEnvelope κ B := by
    rw [Real.log_mul (ne_of_gt hc) (pow_ne_zero _ (ne_of_gt hb)),Real.log_pow]
    dsimp [logEnvelope]
    norm_num
  constructor
  · exact (Real.log_le_log
      (zero_lt_one.trans_le (ActualFirstChartLabelTail318.labelHeight_one κ B _)) hf).trans_eq he
  · exact (Real.log_le_log
      (zero_lt_one.trans_le (ActualQuarticLabelHeight318.labelHeight_one κ B _)) hs).trans_eq he

/-- Both actual chart budgets at the constructed source radius6B.
The distinct true quartic and valid first-chart area constants are added
only here, after their separate source identifications. -/
@[expose] def combinedBudget (κ : ℤ) (B : ℕ) (T : ℝ) (Y : ℕ) : ℝ :=
  (113246208*(B:ℝ)^3/(Y:ℝ))*Real.log (Y:ℝ)+
    25930800*(B:ℝ)^2*T*logEnvelope κ B+25401600*(B:ℝ)^2*T*Real.log (Y:ℝ)

lemma actual_combined_budget (κ : ℤ) (B : ℕ) (hB : 1≤B) (T : ℝ) (hT : 0≤T) (Y : ℕ) :
    goodBudget B κ false T Y+goodBudget B κ true T Y≤combinedBudget κ B T Y := by
  obtain ⟨hf,hs⟩ := actual_log_heights κ B hB
  have hfm := mul_le_mul_of_nonneg_left hf (by positivity : 0≤480200*(6*(B:ℝ))^2*T)
  have hsm := mul_le_mul_of_nonneg_left hs (by positivity : 0≤240100*(6*(B:ℝ))^2*T)
  change ActualFirstChartLabelTail318.labelBudget κ B (6*(B:ℝ)) T Y+
    ActualQuarticLabelHeight318.labelBudget κ B (6*(B:ℝ)) T Y≤_
  dsimp [ActualFirstChartLabelTail318.labelBudget,ActualQuarticLabelHeight318.labelBudget,combinedBudget]
  nlinarith only [hfm,hsm]

end ActualGaussianLogBudget318
