module
public import ActualOriginalRationalDistanceSeparation318
public section
noncomputable section
namespace ActualOriginalRationalFrequencyCancellation318
open ActualOriginalRationalDistanceSeparation318 ActualOriginalReciprocalDistance318
open ActualOriginalWeightedLinearCancellation318 ActualOriginalFiniteAbel318

/-- A centered integer is PRODUCED at each actual frequency, including
half-integer ties. There is no missing nearest-integer hypothesis. -/
lemma actual_centered_integer (x : ℝ) : ∃ m : ℤ, |x-(m : ℝ)|≤1/2 := by
  refine ⟨⌊x+1/2⌋,abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := Int.floor_le (x+1/2)
    linarith
  · have hh := Int.lt_floor_add_one (x+1/2)
    linarith

/-- Rational approximation plus coprimality and the exact frequency
range PRODUCE nonresonance and a denominator-q chord bound. Multiples of
q are deliberately excluded, not assigned an invalid reciprocal estimate. -/
theorem actual_rational_frequency_bound (a q c : ℤ) (t : ℝ) (hq : 0<q)
    (ha : IsCoprime q a) (hc : ¬q∣c)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (hsize : |(c : ℝ)|≤(q : ℝ)/2) :
    fourier c (t : AddCircle (1 : ℝ))≠1 ∧
      2/‖fourier c (t : AddCircle (1 : ℝ))-1‖≤(q : ℝ) := by
  obtain ⟨m,hm⟩ := actual_centered_integer ((c : ℝ)*t)
  have hd := actual_rational_block_separation a q c t hq ha hc ht hsize m
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hp : 0<|(c : ℝ)*t-(m : ℝ)| := lt_of_lt_of_le (by positivity) hd
  obtain ⟨hn,hb⟩ := actual_frequency_reciprocal_bound c m t hm (abs_pos.mp hp)
  refine ⟨hn,hb.trans ?_⟩
  apply (div_le_iff₀ (by positivity : 0<2*|(c : ℝ)*t-(m : ℝ)|)).mpr
  have hd' := (div_le_iff₀ (by positivity : (0 : ℝ)<2*q)).mp hd
  nlinarith

/-- The produced rational separation is consumed by the actual arbitrary
weighted interval sum, with its full endpoint-plus-variation cost. -/
theorem actual_rational_weighted_interval (a q c : ℤ) (t : ℝ) (hq : 0<q)
    (ha : IsCoprime q a) (hc : ¬q∣c)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (hsize : |(c : ℝ)|≤(q : ℝ)/2) (g : ℕ → ℂ) (N : ℕ) :
    ‖weightedLinearInterval c 0 g (N+1) (t : AddCircle (1 : ℝ))‖≤
      min ((N : ℝ)+1) (q : ℝ)*variation g N := by
  obtain ⟨hn,hb⟩ := actual_rational_frequency_bound a q c t hq ha hc ht hsize
  apply (actual_weighted_linear_cancellation c 0 g N _ hn).trans
  exact mul_le_mul_of_nonneg_right (min_le_min le_rfl hb) (variation_nonneg g N)

end ActualOriginalRationalFrequencyCancellation318
