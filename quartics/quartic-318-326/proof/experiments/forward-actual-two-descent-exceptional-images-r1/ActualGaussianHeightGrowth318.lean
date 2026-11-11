module
public import ActualGaussianTwoChartTail318
public section
noncomputable section
namespace ActualGaussianHeightGrowth318
open ActualQuarticCoefficientHeight318 ActualQuarticUniformHeight318
open OriginalUniformEliminantHeight318 OriginalAffineRectangleTail318
set_option maxHeartbeats 14000000

/-- All constants depend ONLY on the fixed original kappa. The number2088
is exactly58*(6)^2 from the actual source radius, not a free geometry input. -/
@[expose] def innerConstant (κ : ℤ) : ℝ := (2*|(κ:ℝ)|+2)*2088^2+8
@[expose] def formConstant (κ : ℤ) : ℝ := (8*|(κ:ℝ)|+4)*2088^2+4
@[expose] def factorConstant : ℝ := 2*2088^2+4
@[expose] def coefficientConstant (κ : ℤ) : ℝ :=
  1+formConstant κ+8*((innerConstant κ)^2+4*2088^2)
@[expose] def firstConstant (κ : ℤ) : ℝ :=
  1+8*(formConstant κ)^2*factorConstant^2+4*2088^4+4*2088^2
@[expose] def secondConstant (κ : ℤ) : ℝ := 1+294^2*109*(coefficientConstant κ)^9
@[expose] def heightConstant (κ : ℤ) : ℝ := 1+firstConstant κ+secondConstant κ

lemma constants_nonneg (κ : ℤ) :
    0≤innerConstant κ ∧ 0≤formConstant κ ∧ 0≤factorConstant ∧
      0≤coefficientConstant κ ∧ 0≤firstConstant κ ∧ 0≤secondConstant κ := by
  dsimp [innerConstant,formConstant,factorConstant,coefficientConstant,firstConstant,secondConstant]
  exact ⟨by positivity,by positivity,by positivity,by positivity,by positivity,by positivity⟩
lemma heightConstant_one (κ : ℤ) : 1≤heightConstant κ := by
  obtain ⟨_,_,_,_,hf,hs⟩ := constants_nonneg κ
  dsimp [heightConstant]
  linarith

lemma source_coefficient_bounds (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    formHeight κ (2*B:ℤ) (2088*(B:ℝ)^2)≤formConstant κ*(B:ℝ)^5 ∧
    factorHeight (2*B:ℤ) (2088*(B:ℝ)^2)≤factorConstant*(B:ℝ)^4 ∧
    innerHeight κ (2*B:ℤ) (2088*(B:ℝ)^2)≤innerConstant κ*(B:ℝ)^4 := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hb0 : (0:ℝ)≤B := by positivity
  have h14 : (B:ℝ)≤(B:ℝ)^4 := by simpa using pow_le_pow_right₀ hb (by norm_num : 1≤4)
  have h15 : (B:ℝ)≤(B:ℝ)^5 := by simpa using pow_le_pow_right₀ hb (by norm_num : 1≤5)
  have h24 : (B:ℝ)^2≤(B:ℝ)^4 := pow_le_pow_right₀ hb (by norm_num)
  have h45 : (B:ℝ)^4≤(B:ℝ)^5 := pow_le_pow_right₀ hb (by norm_num)
  have hκ45 := mul_le_mul_of_nonneg_left h45 (abs_nonneg (κ:ℝ))
  constructor
  · dsimp [formHeight,formConstant]
    push_cast
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2*(B:ℝ))]
    nlinarith only [h15,h45,hκ45]
  constructor
  · dsimp [factorHeight,factorConstant]
    push_cast
    nlinarith only [h24]
  · dsimp [innerHeight,innerConstant]
    push_cast
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2*(B:ℝ))]
    nlinarith only [h14,h24]

lemma actual_coefficient_growth (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    coefficientHeight κ (2*B:ℤ) (2088*(B:ℝ)^2)≤coefficientConstant κ*(B:ℝ)^8 := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  obtain ⟨hf,hn,hj⟩ := source_coefficient_bounds κ B hB
  have hj0 : 0≤innerHeight κ (2*B:ℤ) (2088*(B:ℝ)^2) := by dsimp [innerHeight];positivity
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  obtain ⟨_,hF,_,_,_,_⟩ := constants_nonneg κ
  have h58 := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hb (by norm_num : 5≤8)) hF
  have h68 : (B:ℝ)^6≤(B:ℝ)^8 := pow_le_pow_right₀ hb (by norm_num)
  have h08 : (1:ℝ)≤(B:ℝ)^8 := one_le_pow₀ hb
  dsimp [coefficientHeight,quarticHeight,coefficientConstant]
  push_cast
  nlinarith only [hf,hj2,h58,h68,h08]

/-- Exact actual first-chart numerical height has degree at most18 inB. -/
lemma actual_first_height_growth (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    ActualFirstChartLabelTail318.labelHeight κ B (6*(B:ℝ))≤firstConstant κ*(B:ℝ)^18 := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  obtain ⟨hf,hn,_⟩ := source_coefficient_bounds κ B hB
  have hf0 : 0≤formHeight κ (2*B:ℤ) (2088*(B:ℝ)^2) := by dsimp [formHeight];positivity
  have hn0 : 0≤factorHeight (2*B:ℤ) (2088*(B:ℝ)^2) := by dsimp [factorHeight];positivity
  have hf2 := pow_le_pow_left₀ hf0 hf 2
  have hn2 := pow_le_pow_left₀ hn0 hn 2
  have hm := mul_le_mul hf2 hn2 (sq_nonneg _) (sq_nonneg _)
  have h0 : (1:ℝ)≤(B:ℝ)^18 := one_le_pow₀ hb
  have h8 : (B:ℝ)^8≤(B:ℝ)^18 := pow_le_pow_right₀ hb (by norm_num)
  have h6 : (B:ℝ)^6≤(B:ℝ)^18 := pow_le_pow_right₀ hb (by norm_num)
  have hL : 58*(6*(B:ℝ))^2=2088*(B:ℝ)^2 := by ring
  simp only [ActualFirstChartLabelTail318.labelHeight,OriginalUniformGoodHeight318.globalHeight,hL]
  dsimp [bothHeight,regularHeight,exceptionalHeight,firstConstant]
  push_cast
  nlinarith only [hm,h0,h8,h6]

/-- The corrected true-quartic height has degree at most74. This includes
the actual finite offset-area factor and all nine powers of the TRUE
quartic eliminant coefficient ceiling, not the older quadratic D ceiling. -/
lemma actual_second_height_growth (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    ActualQuarticLabelHeight318.labelHeight κ B (6*(B:ℝ))≤secondConstant κ*(B:ℝ)^74 := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hc := actual_coefficient_growth κ B hB
  have hp := pow_le_pow_left₀ (coefficient_nonneg κ (2*B:ℤ) (2088*(B:ℝ)^2)) hc 9
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0≤294^2*(B:ℝ)^2*109)
  have h0 : (1:ℝ)≤(B:ℝ)^74 := one_le_pow₀ hb
  have hL : 58*(6*(B:ℝ))^2=2088*(B:ℝ)^2 := by ring
  simp only [ActualQuarticLabelHeight318.labelHeight,ActualQuarticUniformFrame318.globalHeight,hL,pointHeight]
  dsimp [secondConstant]
  nlinarith only [hm,h0]

lemma both_heights_growth (κ : ℤ) (B : ℕ) (hB : 1≤B) :
    ActualFirstChartLabelTail318.labelHeight κ B (6*(B:ℝ))≤heightConstant κ*(B:ℝ)^74 ∧
    ActualQuarticLabelHeight318.labelHeight κ B (6*(B:ℝ))≤heightConstant κ*(B:ℝ)^74 := by
  obtain ⟨_,_,_,_,hf,hs⟩ := constants_nonneg κ
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by norm_num : 18≤74)) hf
  have hc1 : firstConstant κ≤heightConstant κ := by dsimp [heightConstant];linarith
  have hc2 : secondConstant κ≤heightConstant κ := by dsimp [heightConstant];linarith
  exact ⟨(actual_first_height_growth κ B hB).trans (hp.trans
    (mul_le_mul_of_nonneg_right hc1 (by positivity))),
    (actual_second_height_growth κ B hB).trans (mul_le_mul_of_nonneg_right hc2 (by positivity))⟩

end ActualGaussianHeightGrowth318
