module
public import ActualOriginalRationalCanonicalSlices318
public section
noncomputable section
namespace ActualOriginalRationalFrequencySpacing318
open ActualOriginalRationalDistanceSeparation318

/-- Two distinct frequency points in a short block inherit arithmetic
separation from their actual difference. All integer translates are covered;
this is the input for subsequent spacing/reciprocal-sum arguments. -/
theorem actual_rational_frequency_spacing (a q c d : ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hn : ¬q∣c-d)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (hsize : |((c-d : ℤ) : ℝ)|≤(q : ℝ)/2) (m : ℤ) :
    1/(2*(q : ℝ))≤|((c : ℝ)*t-(d : ℝ)*t)-(m : ℝ)| := by
  simpa only [Int.cast_sub,sub_mul] using
    actual_rational_block_separation a q (c-d) t hq ha hn ht hsize m

/-- A nonzero difference shorter than q cannot be a multiple of q.
The exact endpoint restriction is retained rather than assuming injective residues. -/
lemma actual_short_difference_not_multiple (q c d : ℤ) (hq : 0<q)
    (hne : c≠d) (hsmall : |c-d|<q) : ¬q∣c-d := by
  rintro ⟨k,hk⟩
  have hk0 : k≠0 := by
    intro h
    rw [h,mul_zero] at hk
    exact hne (sub_eq_zero.mp hk)
  have hkabs : (1 : ℤ)≤|k| := by omega
  have hqabs : |q|=q := abs_of_pos hq
  rw [hk,abs_mul,hqabs] at hsmall
  nlinarith

/-- Every distinct pair in an actual integer interval of diameter at most
q/2 satisfies the required residue exclusion. No coprimality of c or d is
assumed, and no integer translate is omitted. -/
theorem actual_rational_short_block_spacing (a q lo hi c d : ℤ) (t : ℝ)
    (hq : 0<q) (ha : IsCoprime q a)
    (hc : c∈Finset.Icc lo hi) (hd : d∈Finset.Icc lo hi) (hne : c≠d)
    (hdiam : 2*(hi-lo)≤q)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (m : ℤ) :
    1/(2*(q : ℝ))≤|((c : ℝ)*t-(d : ℝ)*t)-(m : ℝ)| := by
  have hc' := Finset.mem_Icc.mp hc
  have hd' := Finset.mem_Icc.mp hd
  have habs : |c-d|≤hi-lo := by omega
  have hsmall : |c-d|<q := by omega
  have hs : (2 : ℤ)*|c-d|≤q := by omega
  have hs' : (2 : ℝ)*|(c : ℝ)-(d : ℝ)|≤(q : ℝ) := by exact_mod_cast hs
  refine actual_rational_frequency_spacing a q c d t hq ha
    (actual_short_difference_not_multiple q c d hq hne hsmall) ht ?_ m
  rw [Int.cast_sub]
  linarith

end ActualOriginalRationalFrequencySpacing318
