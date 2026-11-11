module
public import ActualOriginalUnitCoefficientCRT318
public import Mathlib.NumberTheory.EulerProduct.Basic
public section
noncomputable section
namespace ActualOriginalGlobalCoefficient318
open ActualOriginalUnitFourierLayers318 ActualOriginalUnitCoefficientCRT318
open ActualOriginalCompleteFourierCount318 QuadricCRTAssembly318
set_option maxHeartbeats 16000000

/-- Zero is excluded from the denominator series by assigning it0.
Every positive denominator retains the literal q^-5 IsUnit character sum. -/
@[expose] def coefficient (κ : ℤ) (q : ℕ) : ℂ :=
  if h : q=0 then 0 else
    letI : NeZero q := ⟨h⟩
    unitAverage κ q

lemma actual_coefficient_zero (κ : ℤ) : coefficient κ 0 = 0 := by simp [coefficient]
lemma actual_coefficient_nonzero (κ : ℤ) (q : ℕ) [NeZero q] :
    coefficient κ q = unitAverage κ q := by simp [coefficient,NeZero.ne q]

lemma actual_coefficient_one (κ : ℤ) : coefficient κ 1 = 1 := by
  rw [actual_coefficient_nonzero,actual_unit_average_one]
  simp [completeAverage,completeSum,Coordinates,equation]

lemma actual_coefficient_coprime (κ : ℤ) {m n : ℕ} (h : m.Coprime n) :
    coefficient κ (m*n)=coefficient κ m*coefficient κ n := by
  by_cases hm : m=0
  · subst m
    simp only [zero_mul,actual_coefficient_zero]
  by_cases hn : n=0
  · subst n
    simp only [mul_zero,actual_coefficient_zero]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  simp only [actual_coefficient_nonzero]
  exact actual_original_unit_coefficient_coprime κ m n h

end ActualOriginalGlobalCoefficient318
