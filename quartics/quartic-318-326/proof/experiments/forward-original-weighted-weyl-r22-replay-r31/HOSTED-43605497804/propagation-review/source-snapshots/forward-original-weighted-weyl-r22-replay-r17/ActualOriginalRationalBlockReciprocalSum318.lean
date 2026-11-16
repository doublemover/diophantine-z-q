module
public import ActualOriginalReciprocalBinBudget318
public section
noncomputable section
namespace ActualOriginalRationalBlockReciprocalSum318
open ActualOriginalCenteredFrequencyBins318 ActualOriginalReciprocalBinBudget318
open ActualOriginalReciprocalDistance318
open scoped BigOperators

/-- The actual finite-length Fourier cancellation kernel, with an
explicit full-length cost at resonance. -/
@[expose] def fourierChordCap (N : ℝ) (c : ℤ) (t : ℝ) : ℝ :=
  if fourier c (t : AddCircle (1 : ℝ))=1 then N
    else min N (2/‖fourier c (t : AddCircle (1 : ℝ))-1‖)

lemma actual_chord_cap_le (N : ℝ) (c : ℤ) (t : ℝ) : fourierChordCap N c t≤N := by
  unfold fourierChordCap
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma actual_chord_cap_centered (N : ℝ) (c : ℤ) (t : ℝ) :
    fourierChordCap N c t≤reciprocalCap N (centeredValue ((c : ℝ)*t)) := by
  by_cases hz : centeredValue ((c : ℝ)*t)=0
  · rw [reciprocalCap,if_pos hz]
    exact actual_chord_cap_le N c t
  have hm : |(c : ℝ)*t-(centeredInteger ((c : ℝ)*t) : ℝ)|≤1/2 :=
    actual_centered_value_bound ((c : ℝ)*t)
  obtain ⟨hn,hb⟩ := actual_frequency_reciprocal_bound c (centeredInteger ((c : ℝ)*t)) t hm hz
  rw [fourierChordCap,if_neg hn,reciprocalCap,if_neg hz]
  exact min_le_min le_rfl hb

/-- The COMPLETE reciprocal/chord sum in every controlled short block
has an explicit harmonic-shaped bin budget. Rational resonances are retained
with cost N. This does not yet partition all original displacements. -/
theorem actual_rational_short_block_chord_budget (a q lo hi : ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hdiam : 2*(hi-lo)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    (∑ c∈Finset.Icc lo hi, fourierChordCap N c t)≤
      ∑ b∈Finset.Icc (-q) q, binCost N q b := by
  apply (Finset.sum_le_sum (fun c hc => actual_chord_cap_centered N c t)).trans
  apply actual_finite_reciprocal_bin_budget (Finset.Icc lo hi)
    (fun c => centeredValue ((c : ℝ)*t)) N q hN hq
  · exact actual_frequency_bin_injective a q lo hi t hq ha hdiam ht
  · intro c hc
    exact actual_frequency_bin_range q c t hq

end ActualOriginalRationalBlockReciprocalSum318
