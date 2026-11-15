module
public import ActualQuarticIndexedFamily318
public section
noncomputable section
namespace ActualQuarticLabelHeight318
open ActualQuarticCoefficientHeight318 ActualQuarticUniformHeight318 ActualQuarticUniformFrame318
open OriginalUniformEliminantHeight318 OriginalGlobalBadMass318
set_option maxHeartbeats 10000000

/-- Monotonicity in the absolute label applies ONLY to the numerical
height ceiling. No source polynomial, lattice or obstruction is relabeled. -/
lemma coefficient_abs_mono (κ t s : ℤ) (L : ℝ) (hts : |(t:ℝ)|≤|(s:ℝ)|) :
    coefficientHeight κ t L≤coefficientHeight κ s L := by
  have hsq : (t:ℝ)^2≤(s:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t:ℝ)) hts 2
  have hj : innerHeight κ t L≤ innerHeight κ s L := by dsimp [innerHeight];linarith
  have hj0 : 0≤ innerHeight κ t L := by dsimp [innerHeight];positivity
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have htl := mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
  have hq : quarticHeight κ t L≤quarticHeight κ s L := by dsimp [quarticHeight];linarith
  have hf : formHeight κ t L≤formHeight κ s L := by
    dsimp [formHeight]
    gcongr <;> exact hts
  dsimp [coefficientHeight]
  linarith

lemma global_abs_mono (κ t s : ℤ) (R : ℝ) (hts : |(t:ℝ)|≤|(s:ℝ)|) :
    globalHeight κ t R≤globalHeight κ s R := by
  have hc := coefficient_abs_mono κ t s (58*R^2) hts
  have hp := pow_le_pow_left₀ (coefficient_nonneg κ t (58*R^2)) hc 9
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0:ℝ)≤109)) (sq_nonneg (49*R))
  dsimp [globalHeight,pointHeight]
  linarith only [hh]

/-- The endpoint 2B is a uniform numerical height argument only. Original
signed labels and their q(t) lattices remain unchanged in every count. -/
@[expose] def labelHeight (κ : ℤ) (B : ℕ) (R : ℝ) : ℝ :=
  globalHeight κ (2*B:ℤ) R
lemma labelHeight_one (κ : ℤ) (B : ℕ) (R : ℝ) : 1≤labelHeight κ B R :=
  global_one κ (2*B:ℤ) R

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
    240100*R^2*T*Real.log (labelHeight κ B R)+352800*R^2*T*Real.log (Y:ℝ)

lemma labelBudget_nonneg (κ : ℤ) (B : ℕ) (R T : ℝ) (hR : 0≤R) (hT : 0≤T)
    (Y : ℕ) (hY : 3≤Y) : 0≤labelBudget κ B R T Y := by
  have hl := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hg := Real.log_nonneg (labelHeight_one κ B R)
  dsimp [labelBudget]
  positivity

lemma actual_label_budget (κ t : ℤ) (B : ℕ) (ht : t∈labels B) (R T : ℝ)
    (hT : 0≤T) (Y : ℕ) : uniformBudget κ t R T Y≤labelBudget κ B R T Y := by
  have hh := Real.log_le_log (zero_lt_one.trans_le (global_one κ t R))
    (actual_label_height κ t B ht R)
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0≤240100*R^2*T)
  dsimp [uniformBudget,labelBudget]
  linarith only [hm]

end ActualQuarticLabelHeight318
