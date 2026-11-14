module
public import ActualOriginalEvenDisplacementFrequencyBudget318
public section
noncomputable section
namespace ActualOriginalScaledDisplacementBlockCount318
open ActualOriginalFrequencyBlockPartition318 ActualOriginalCompleteFrequencyBudget318
open ActualOriginalEvenDisplacementFrequencyBudget318 ActualOriginalRationalBlockReciprocalSum318
open scoped BigOperators

lemma actual_quotient_endpoint_count (L lo hi : ℤ) (hL : 0<L) (horder : lo≤hi) :
    ((hi/L-lo/L+1).toNat : ℝ)≤((hi : ℝ)-(lo : ℝ))/(L : ℝ)+2 := by
  have hmono := Int.ediv_le_ediv hL horder
  have hk : (0 : ℤ)≤hi/L-lo/L+1 := by omega
  have hcast : ((hi/L-lo/L+1).toNat : ℝ)=((hi/L : ℤ) : ℝ)-((lo/L : ℤ) : ℝ)+1 := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have htop : ((hi/L : ℤ) : ℝ)*(L : ℝ)≤(hi : ℝ) := by
    exact_mod_cast Int.ediv_mul_le hi (ne_of_gt hL)
  have hbottom : (lo : ℝ)-(L : ℝ)<((lo/L : ℤ) : ℝ)*(L : ℝ) := by
    exact_mod_cast Int.lt_ediv_mul lo hL
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  rw [hcast]
  calc
    _ ≤ ((hi : ℝ)-(lo : ℝ)+2*(L : ℝ))/(L : ℝ) :=
      (le_div_iff₀ hLr).mpr (by nlinarith)
    _ = _ := by field_simp; ring

/-- The produced block length is at least q/2, giving an explicit
O(interval-width/q+1) count rather than leaving a finite cardinal abstract. -/
lemma actual_rational_endpoint_count (q lo hi : ℤ) (hq : 0<q) (horder : lo≤hi) :
    ((hi/rationalBlockLength q-lo/rationalBlockLength q+1).toNat : ℝ)≤
      2*((hi : ℝ)-(lo : ℝ))/(q : ℝ)+2 := by
  have hL := (actual_rational_block_length q hq).1
  apply (actual_quotient_endpoint_count (rationalBlockLength q) lo hi hL horder).trans
  apply add_le_add_right _ 2
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hLi : (0 : ℝ)<rationalBlockLength q := by exact_mod_cast hL
  have hwidth : (0 : ℝ)≤(hi : ℝ)-(lo : ℝ) := by exact_mod_cast sub_nonneg.mpr horder
  have hlength : q≤2*rationalBlockLength q := by unfold rationalBlockLength; omega
  have hlength' : (q : ℝ)≤2*(rationalBlockLength q : ℝ) := by exact_mod_cast hlength
  apply (div_le_div_iff₀ hLi hqi).mpr
  have hm := mul_le_mul_of_nonneg_left hlength' hwidth
  nlinarith

/-- Quantitative COMPLETE sum at the literal even displacement frequencies.
This is the first-axis kernel only; no four outer directions disappear. -/
theorem actual_scaled_even_displacement_budget (a q H : ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hH : 0≤H)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    (∑ h∈Finset.Icc (-2*H) (2*H), fourierChordCap N (2*h) t)≤
      (16*(H : ℝ)/(q : ℝ)+2)*reciprocalBlockBudget N q := by
  apply (actual_even_displacement_frequency_budget a q H t N hq ha ht hN).trans
  apply mul_le_mul_of_nonneg_right _ (actual_reciprocal_block_budget_nonneg N q hN hq)
  have hc := actual_rational_endpoint_count q (-4*H) (4*H) hq (by omega)
  convert hc using 1 <;> push_cast <;> ring

end ActualOriginalScaledDisplacementBlockCount318
