module
public import ActualOriginalRationalFrequencySpacing318
public section
noncomputable section
namespace ActualOriginalCenteredFrequencyBins318
open ActualOriginalRationalFrequencySpacing318

@[expose] def centeredInteger (x : ℝ) : ℤ := ⌊x+1/2⌋
@[expose] def centeredValue (x : ℝ) : ℝ := x-(centeredInteger x : ℝ)
@[expose] def frequencyBin (q c : ℤ) (t : ℝ) : ℤ := ⌊2*(q : ℝ)*centeredValue ((c : ℝ)*t)⌋

lemma actual_centered_value_bound (x : ℝ) : |centeredValue x|≤1/2 := by
  unfold centeredValue centeredInteger
  apply abs_le.mpr
  have h1 := Int.floor_le (x+1/2)
  have h2 := Int.lt_floor_add_one (x+1/2)
  constructor <;> linarith

lemma actual_frequency_bin_range (q c : ℤ) (t : ℝ) (hq : 0<q) :
    frequencyBin q c t∈Finset.Icc (-q) q := by
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hx := abs_le.mp (actual_centered_value_bound ((c : ℝ)*t))
  have hxlo := mul_le_mul_of_nonneg_left hx.1 (by positivity : (0 : ℝ)≤2*q)
  have hxhi := mul_le_mul_of_nonneg_left hx.2 (by positivity : (0 : ℝ)≤2*q)
  have hl := Int.floor_le (2*(q : ℝ)*centeredValue ((c : ℝ)*t))
  have hu := Int.lt_floor_add_one (2*(q : ℝ)*centeredValue ((c : ℝ)*t))
  change (frequencyBin q c t : ℝ)≤_ at hl
  change _<(frequencyBin q c t : ℝ)+1 at hu
  have hb : (-(q : ℝ))-1<(frequencyBin q c t : ℝ) ∧
      (frequencyBin q c t : ℝ)≤(q : ℝ) := by constructor <;> nlinarith
  have hb' : -q-1<frequencyBin q c t ∧ frequencyBin q c t≤q := by exact_mod_cast hb
  apply Finset.mem_Icc.mpr
  omega

lemma actual_centered_pair_spacing (a q lo hi c d : ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a)
    (hc : c∈Finset.Icc lo hi) (hd : d∈Finset.Icc lo hi) (hne : c≠d)
    (hdiam : 2*(hi-lo)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) :
    1/(2*(q : ℝ))≤|centeredValue ((c : ℝ)*t)-centeredValue ((d : ℝ)*t)| := by
  have hs := actual_rational_short_block_spacing a q lo hi c d t hq ha hc hd hne hdiam ht
    (centeredInteger ((c : ℝ)*t)-centeredInteger ((d : ℝ)*t))
  have he : centeredValue ((c : ℝ)*t)-centeredValue ((d : ℝ)*t)=
      ((c : ℝ)*t-(d : ℝ)*t)-
        ((centeredInteger ((c : ℝ)*t)-centeredInteger ((d : ℝ)*t) : ℤ) : ℝ) := by
    unfold centeredValue
    push_cast
    ring
  rw [he]
  exact hs

/-- The complete short block injects into literal integer bins. This
includes a possible exact resonance; it is not discarded from the index set. -/
theorem actual_frequency_bin_injective (a q lo hi : ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hdiam : 2*(hi-lo)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) :
    Set.InjOn (fun c : ℤ => frequencyBin q c t) (Finset.Icc lo hi : Set ℤ) := by
  intro c hc d hd he
  by_contra hne
  have hs := actual_centered_pair_spacing a q lo hi c d t hq ha hc hd hne hdiam ht
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hsep := (div_le_iff₀ (by positivity : (0 : ℝ)<2*q)).mp hs
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor he
  have hid : 2*(q : ℝ)*centeredValue ((c : ℝ)*t)-
      2*(q : ℝ)*centeredValue ((d : ℝ)*t)=
      (2*(q : ℝ))*(centeredValue ((c : ℝ)*t)-centeredValue ((d : ℝ)*t)) := by ring
  rw [hid,abs_mul,abs_of_pos (by positivity : (0 : ℝ)<2*q)] at hh
  nlinarith

end ActualOriginalCenteredFrequencyBins318
