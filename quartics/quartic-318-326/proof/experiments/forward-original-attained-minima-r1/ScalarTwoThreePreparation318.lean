module
public import ScalarHalfTraceDepth318
public section
noncomputable section
namespace ScalarTwoThreePreparation318
open CoherentMultipleCharts318 GeneratorScalarProgression318 ScalarTranslatedIndex318
open ScalarIndexValuations318 ScalarHalfTraceDepth318 ScalarForwardWitness318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

lemma input_values (a : ℤ) : padicValRat 2 (inputR (a:ℚ))=2 ∧
    padicValRat 3 (inputR (a:ℚ))=0 ∧ padicValRat 17 (inputR (a:ℚ))=0 := by
  obtain ⟨h₂,h₃,h₁₇⟩ := ScalarSmallPrimePreparation318.actual_multiplier_values a
  have hr : inputR (a:ℚ)≠0 := ne_of_gt (lt_trans (by norm_num) (integer_inputR_large a))
  have v₂ : padicValRat 2 (114444:ℚ)=2 := by
    convert ScalarSmallPrimePreparation318.value_scaled_unit 2 2 28611 (by norm_num) using 1 <;> norm_num
  have v₃ : padicValRat 3 (114444:ℚ)=2 := by
    convert ScalarSmallPrimePreparation318.value_scaled_unit 3 2 12716 (by norm_num) using 1 <;> norm_num
  have v₁₇ : padicValRat 17 (114444:ℚ)=2 := by
    convert ScalarSmallPrimePreparation318.value_scaled_unit 17 2 396 (by norm_num) using 1 <;> norm_num
  rw [padicValRat.mul (by norm_num) hr,v₂] at h₂
  rw [padicValRat.mul (by norm_num) hr,v₃] at h₃
  rw [padicValRat.mul (by norm_num) hr,v₁₇] at h₁₇
  omega

lemma common_norm_ne (h : ℤ) (hh : h≠0) : normCoefficient (chartU h)≠0 := by
  rw [norm_coefficient]
  exact AnchorNorm318.norm_ne_zero (fun hz => hh ((chartU_zero_iff h).mp hz))

/-- Concrete integer-index depth at2, with the exact offset15 arising from
r's order2 and the original r^15 denominator. No packed-unit hypothesis. -/
theorem unit_two (a : ℤ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hh : h≠0) (hn : labels 1≠0) (hn1 : labels 1≠1)
    (hdepth : padicValInt 2 h+15≤padicValInt 2 (labels 1-1)) :
    padicValRat 2 (W (DetectorGateWitness318.witness (a:ℚ) labels h) (labels 1))=0 := by
  let w := DetectorGateWitness318.witness (a:ℚ) labels h
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have hH : w 37≠0 := by rw [ScalarActualInputs318.detector37]; exact common_norm_ne h hh
  have hf : w 33≠0 := by
    rw [ScalarActualInputs318.detector33]
    exact ScalarPackedLocalUnit318.half_trace_ne _ (common_norm_ne h hh)
  have hr : inputR (w 0)≠0 := by rw [hin]; linarith [integer_inputR_large a]
  have hvR : padicValRat 2 (inputR (w 0))=2 := by rw [hin]; exact (input_values a).1
  have hvH : padicValRat 2 (w 37)=3+2*(padicValInt 2 h:ℤ) := by
    rw [ScalarActualInputs318.detector37]
    exact chart_norm_two h hh
  have hvf : padicValRat 2 (w 33)=3+2*(padicValInt 2 h:ℤ) := by
    rw [ScalarActualInputs318.detector33,half_trace_two _ (common_norm_ne h hh)]
    exact chart_norm_two h hh
  have hvI := scalar_norm_two (labels 1) hn hn1
  exact (ScalarPackedLocalUnit318.actual_unit 2 w (labels 1) hr hf hH hn hn1
    (by omega)
    (by rw [padicValRat.mul (by norm_num) hf,padicValRat.self (by norm_num),hvf]; omega)
    (by omega)).2

/-- The corresponding inert3-adic preparation uses the actual half-trace
lower bound and the exact translated index n−1. -/
theorem unit_three (a : ℤ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hh : h≠0) (heven : Even h) (hn : labels 1≠0) (hn1 : labels 1≠1)
    (hneven : Even (labels 1-1))
    (hdepth : padicValInt 3 h<padicValInt 3 (labels 1-1)) :
    padicValRat 3 (W (DetectorGateWitness318.witness (a:ℚ) labels h) (labels 1))=0 := by
  let w := DetectorGateWitness318.witness (a:ℚ) labels h
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have hH : w 37≠0 := by rw [ScalarActualInputs318.detector37]; exact common_norm_ne h hh
  have hf : w 33≠0 := by
    rw [ScalarActualInputs318.detector33]
    exact ScalarPackedLocalUnit318.half_trace_ne _ (common_norm_ne h hh)
  have hr : inputR (w 0)≠0 := by rw [hin]; linarith [integer_inputR_large a]
  have hvR : padicValRat 3 (inputR (w 0))=0 := by rw [hin]; exact (input_values a).2.1
  have hvH : padicValRat 3 (w 37)=2+2*(padicValInt 3 h:ℤ) := by
    rw [ScalarActualInputs318.detector37]
    exact chart_norm_three h hh heven
  have hvf : 2+2*(padicValInt 3 h:ℤ)≤padicValRat 3 (w 33) := by
    rw [ScalarActualInputs318.detector33,←chart_norm_three h hh heven]
    exact half_trace_three _ (common_norm_ne h hh)
  have hvI := scalar_norm_three (labels 1) hn hn1 hneven
  have v₂ : padicValRat 3 (2:ℚ)=0 := by
    simpa using AnchorNorm318.rational_unit_value 3 2 1 (by norm_num) (by norm_num)
  exact (ScalarPackedLocalUnit318.actual_unit 3 w (labels 1) hr hf hH hn hn1
    (by omega)
    (by rw [padicValRat.mul (by norm_num) hf,v₂]; omega)
    (by omega)).2

end ScalarTwoThreePreparation318
