module
public import ActualQuarticLabelHeight318
public section
noncomputable section
namespace ActualQuarticSignedGoodTail318
open scoped BigOperators
open ActualQuarticGoodFamily318 ActualQuarticIndexedFamily318 ActualQuarticLabelHeight318
open OriginalUniformGoodFamily318 (familyWeight)
open OriginalGlobalBadMass318 OriginalSignedLabelRankin318 OriginalUniformEulerRankin318
set_option maxHeartbeats 10000000

lemma familyWeight_nonneg (κ t : ℤ) : 0≤familyWeight κ t := by
  dsimp [familyWeight]
  positivity

/-- The true K count is normalized and the original signed label retained.
Only the explicit logarithmic height ceiling is made uniform over labels. -/
lemma fixed_label_tail (D B : ℕ) (κ t : ℤ) (hκ : κ≠0) (ht : t∈labels B)
    (R T : ℝ) (hR : 0≤R) (hT : 0≤T) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (GoodPoints D κ t R T Y):ℝ)*Real.log (Y:ℝ)≤
      familyWeight κ t*labelBudget κ B R T Y := by
  exact (original_good_uniform_tail D κ t hκ (label_ne_zero B t ht)
    R T hR hT hTR Y hY).trans
      (mul_le_mul_of_nonneg_left (actual_label_budget κ t B ht R T hT Y)
        (familyWeight_nonneg κ t))

@[expose] def signedCount (D B : ℕ) (κ : ℤ) (R T : ℝ) (Y : ℕ) : ℝ :=
  ∑ t∈labels B, (Nat.card (GoodPoints D κ t R T Y):ℝ)

/-- Actual all-signed-label good-point count with the genuine retained-
prime Rankin producer consumed. Excluded-prime powers remain in the
constructed rankinConstant; no B-dependent constant or average is assumed. -/
theorem actual_signed_good_tail (D B : ℕ) (κ : ℤ) (hκ : κ≠0)
    (R T : ℝ) (hR : 0≤R) (hT : 0≤T) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y)
    (δ : ℝ) (hδ : 0<δ) :
    signedCount D B κ R T Y*Real.log (Y:ℝ)≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*labelBudget κ B R T Y := by
  have hs := Finset.sum_le_sum (fun t (ht : t∈labels B) =>
    fixed_label_tail D B κ t hκ ht R T hR hT hTR Y hY)
  have hr := mul_le_mul_of_nonneg_right (actual_original_label_sum κ hκ δ hδ B)
    (labelBudget_nonneg κ B R T hR hT Y hY)
  change (∑ t∈labels B,(Nat.card (GoodPoints D κ t R T Y):ℝ))*Real.log (Y:ℝ)≤_
  rw [Finset.sum_mul]
  exact hs.trans (by simpa only [Finset.sum_mul] using hr)

end ActualQuarticSignedGoodTail318
