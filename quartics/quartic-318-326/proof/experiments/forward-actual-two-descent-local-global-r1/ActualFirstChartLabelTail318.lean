module
public import ActualGaussianWeightedGoodTail318
public section
noncomputable section
namespace ActualFirstChartLabelTail318
open OriginalUniformGoodHeight318 OriginalUniformGoodTail318
open OriginalAffineRectangleTail318
open scoped BigOperators
open OriginalUniformEliminantHeight318 OriginalGlobalBadMass318
set_option maxHeartbeats 10000000

/-- Numerical FIRST-chart height monotonicity only. The valid P/D
estimate is used solely at side=false, where actual source K=P*A+D. -/
lemma global_abs_mono (κ t s : ℤ) (R : ℝ) (hts : |(t:ℝ)|≤|(s:ℝ)|) :
    globalHeight κ t R≤globalHeight κ s R := by
  let L := 58*R^2
  have hsq : (t:ℝ)^2≤(s:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t:ℝ)) hts 2
  have hf : formHeight κ t L≤formHeight κ s L := by
    dsimp [formHeight]
    gcongr <;> exact hts
  have hn : factorHeight t L≤factorHeight s L := by dsimp [factorHeight];linarith
  have hf0 : 0≤formHeight κ t L := by dsimp [formHeight];positivity
  have hn0 : 0≤factorHeight t L := by dsimp [factorHeight];positivity
  have hf2 := pow_le_pow_left₀ hf0 hf 2
  have hn2 := pow_le_pow_left₀ hn0 hn 2
  have hm := mul_le_mul hf2 hn2 (sq_nonneg _) (sq_nonneg _)
  have htL := mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
  change bothHeight κ t L≤bothHeight κ s L
  dsimp [bothHeight,regularHeight,exceptionalHeight]
  nlinarith only [hm,htL]

/-- The endpoint 2B is a uniform numerical height argument only. Original
signed labels and their q(t) lattices remain unchanged in every count. -/
@[expose] def labelHeight (κ : ℤ) (B : ℕ) (R : ℝ) : ℝ :=
  globalHeight κ (2*B:ℤ) R
lemma labelHeight_one (κ : ℤ) (B : ℕ) (R : ℝ) : 1≤labelHeight κ B R :=
  globalHeight_one κ (2*B:ℤ) R

lemma actual_label_height (κ t : ℤ) (B : ℕ) (ht : t∈labels B) (R : ℝ) :
    globalHeight κ t R≤labelHeight κ B R := by
  have hh : |(t:ℝ)|≤2*(B:ℝ) := by
    have hz : |t|≤(2*B:ℤ) := by
      simpa only [Int.natCast_natAbs] using
        (show (t.natAbs:ℤ)≤(2*B:ℤ) by exact_mod_cast label_bound B t ht)
    exact_mod_cast hz
  apply global_abs_mono κ t (2*B:ℤ) R
  simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    abs_of_nonneg (by positivity : (0:ℝ)≤2*(B:ℝ))] using hh

@[expose] def labelBudget (κ : ℤ) (B : ℕ) (R T : ℝ) (Y : ℕ) : ℝ :=
  (262144*R^3/(Y:ℝ))*Real.log (Y:ℝ)+
    480200*R^2*T*Real.log (labelHeight κ B R)+352800*R^2*T*Real.log (Y:ℝ)

lemma labelBudget_nonneg (κ : ℤ) (B : ℕ) (R T : ℝ) (hR : 0≤R) (hT : 0≤T)
    (Y : ℕ) (hY : 3≤Y) : 0≤labelBudget κ B R T Y := by
  have hl := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hg := Real.log_nonneg (labelHeight_one κ B R)
  dsimp [labelBudget]
  positivity

lemma actual_label_budget (κ t : ℤ) (B : ℕ) (ht : t∈labels B) (R T : ℝ)
    (hT : 0≤T) (Y : ℕ) : uniformBudget κ t R T Y≤labelBudget κ B R T Y := by
  have hh := Real.log_le_log (zero_lt_one.trans_le (globalHeight_one κ t R))
    (actual_label_height κ t B ht R)
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0≤480200*R^2*T)
  dsimp [uniformBudget,labelBudget]
  linarith only [hm]



open OriginalUniformGoodFamily318 (familyWeight)
open OriginalSignedLabelRankin318 OriginalUniformEulerRankin318
lemma familyWeight_nonneg (κ t : ℤ) : 0≤familyWeight κ t := by
  dsimp [familyWeight]
  positivity

/-- The valid FIRST-chart P/D count is normalized and the original signed label retained.
Only the explicit logarithmic height ceiling is made uniform over labels. -/
lemma fixed_label_tail (D B : ℕ) (κ t : ℤ) (hκ : κ≠0) (ht : t∈labels B)
    (R T : ℝ) (hR : 0≤R) (hT : 0≤T) (hTR : T≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (OriginalGoodAllPrimeFamily318.GoodPoints D false κ t R T Y):ℝ)*Real.log (Y:ℝ)≤
      familyWeight κ t*labelBudget κ B R T Y := by
  exact (OriginalUniformGoodFamily318.original_good_uniform_tail D false κ t hκ
    R T hR hT hTR Y hY).trans
      (mul_le_mul_of_nonneg_left (actual_label_budget κ t B ht R T hT Y)
        (familyWeight_nonneg κ t))

@[expose] def signedCount (D B : ℕ) (κ : ℤ) (R T : ℝ) (Y : ℕ) : ℝ :=
  ∑ t∈labels B, (Nat.card (OriginalGoodAllPrimeFamily318.GoodPoints D false κ t R T Y):ℝ)

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
  change (∑ t∈labels B,(Nat.card (OriginalGoodAllPrimeFamily318.GoodPoints D false κ t R T Y):ℝ))*Real.log (Y:ℝ)≤_
  rw [Finset.sum_mul]
  exact hs.trans (by simpa only [Finset.sum_mul] using hr)


end ActualFirstChartLabelTail318
