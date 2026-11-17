module
public import ActualOriginalCharacterCRT318
public section
noncomputable section
namespace ActualOriginalUnitCoefficientCRT318
open QuadricCRTAssembly318 ActualOriginalFrequencyCRT318 ActualOriginalCharacterCRT318
open ActualOriginalUnitFourierLayers318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The original five-coordinate exponential sum splits through the
full residue CRT for each pair of actual cross-scaled frequencies. -/
lemma actual_original_frequency_sum_crt (κ : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod m) (b : ZMod n) :
    (∑ x : Coordinates (ZMod (m*n)),
      ZMod.stdAddChar (frequencyMerge m n h (a,b)*equation (κ : ZMod (m*n)) x)) =
      (∑ x : Coordinates (ZMod m), ZMod.stdAddChar (a*equation (κ : ZMod m) x)) *
        (∑ y : Coordinates (ZMod n), ZMod.stdAddChar (b*equation (κ : ZMod n) y)) := by
  classical
  simp_rw [actual_original_crt_phase]
  rw [Equiv.sum_comp (residueCRT m n h)
    (fun xy : Coordinates (ZMod m) × Coordinates (ZMod n) =>
      ZMod.stdAddChar (a*equation (κ : ZMod m) xy.1) *
        ZMod.stdAddChar (b*equation (κ : ZMod n) xy.2))]
  rw [Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]

/-- Genuine coprime multiplicativity of the conventional unit-frequency
coefficient. Unlike complete-average CRT, both the unit domain and the
standard additive-character multipliers have been explicitly transported. -/
theorem actual_original_unit_coefficient_coprime (κ : ℤ) (m n : ℕ)
    [NeZero m] [NeZero n] (h : m.Coprime n) :
    unitAverage κ (m*n) = unitAverage κ m * unitAverage κ n := by
  classical
  have hs := Equiv.sum_comp (unitFrequencyMerge m n h)
    (fun a : {a : ZMod (m*n) // IsUnit a} =>
      ∑ x : Coordinates (ZMod (m*n)), ZMod.stdAddChar (a.val*equation (κ : ZMod (m*n)) x))
  simp only [actual_unit_frequency_merge_value] at hs
  simp_rw [actual_original_frequency_sum_crt κ m n h] at hs
  rw [Fintype.sum_prod_type] at hs
  simp_rw [←Finset.mul_sum] at hs
  rw [←Finset.sum_mul] at hs
  unfold unitAverage
  rw [←hs]
  push_cast
  rw [mul_pow,mul_div_mul_comm]

end ActualOriginalUnitCoefficientCRT318
