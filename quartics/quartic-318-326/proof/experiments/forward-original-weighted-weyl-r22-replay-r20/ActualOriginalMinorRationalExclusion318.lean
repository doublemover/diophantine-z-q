module
public import ActualOriginalReducedArcIndex318
public section
noncomputable section
namespace ActualOriginalMinorRationalExclusion318
open ActualOriginalMajorArcDomain318 ActualOriginalReducedArcIndex318

/-- A close small-denominator rational to the SHIFTED fundamental interval
must already be canonical. The lower endpoint and the possible lift at 1
are handled, not silently replaced by the usual interval [0,1). -/
lemma actual_close_fraction_canonical (N : ℕ) (hN : 0<N) (B : ℝ)
    (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B) (t : ℝ)
    (ht : t∈fundamental N B) (a q : ℤ) (hq : 0<q) (hqN : q≤N)
    (he : |t-(a : ℝ)/(q : ℝ)|<radius N B) : 0≤a ∧ a<q := by
  have hnr : (0 : ℝ)<N := by exact_mod_cast hN
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hqnr : (q : ℝ)≤N := by exact_mod_cast hqN
  have hr := radius_small N hN B hB hs
  have hrec := one_div_le_one_div_of_le hqr hqnr
  have hb := abs_lt.mp he
  change -radius N B<t ∧ t≤1-radius N B at ht
  have hal : -(1/(q : ℝ))<(a : ℝ)/(q : ℝ) := by linarith
  have hau : (a : ℝ)/(q : ℝ)<1 := by linarith
  have hal' : (-1 : ℝ)<(a : ℝ) := by
    have hh : (-1 : ℝ)/(q : ℝ)<(a : ℝ)/(q : ℝ) := by simpa only [neg_div] using hal
    exact (div_lt_div_iff_of_pos_right hqr).mp hh
  have hai : (-1 : ℤ)<a := by exact_mod_cast hal'
  have haq : (a : ℝ)<(q : ℝ) := (div_lt_one hqr).mp hau
  exact ⟨by omega,by exact_mod_cast haq⟩

/-- Every reduced denominator at most N is excluded with strict radius on
the ACTUAL minor domain. The weak lower bound is deliberate: the original
major arcs are half-open, so equality at a left endpoint is not discarded. -/
theorem actual_minor_small_denominator_error (N : ℕ) (hN : 0<N) (B : ℝ)
    (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B) (t : ℝ)
    (ht : t∈minorDomain N B) (a q : ℤ) (hq : 0<q)
    (hqN : q≤N) (hc : IsCoprime q a) :
    radius N B≤|t-(a : ℝ)/(q : ℝ)| := by
  by_contra h
  have he := lt_of_not_ge h
  obtain ⟨ha,haq⟩ := actual_close_fraction_canonical N hN B hB hs t ht.1 a q hq hqN he
  obtain ⟨i,hi⟩ := actual_reduced_arc_index N a q hq hqN ha haq hc
  apply ht.2
  apply Set.mem_iUnion.mpr
  refine ⟨i,?_⟩
  change center i-radius N B<t ∧ t≤center i+radius N B
  rw [hi]
  have hh := abs_lt.mp he
  constructor <;> linarith

end ActualOriginalMinorRationalExclusion318
