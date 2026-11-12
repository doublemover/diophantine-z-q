module
public import ActualOriginalLineCorrelation318
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public section
noncomputable section
namespace ActualOriginalReciprocalDistance318
open ActualOriginalWeightedLinearCancellation318 ActualOriginalFiniteAbel318

/-- The actual period-one chord has the correct factor four on the
centered fundamental interval. This is Jordan's inequality, not an
assumed Diophantine separation bound. -/
theorem actual_centered_chord_lower (x : ℝ) (hx : |x|≤1/2) :
    4*|x|≤‖fourier (1 : ℤ) (x : AddCircle (1 : ℝ))-1‖ := by
  have hf : fourier (1 : ℤ) (x : AddCircle (1 : ℝ))=
      Complex.exp (Complex.I*((2*Real.pi*x : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one,Int.cast_one,div_one]
    congr 1
    push_cast
    ring
  have hp : |Real.pi*x|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hp
  rw [abs_mul,abs_of_pos Real.pi_pos] at hs
  have he : 2/Real.pi*(Real.pi*|x|)=2*|x| := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [he] at hs
  rw [hf,Complex.norm_exp_I_mul_ofReal_sub_one]
  have ht : 2*Real.pi*x/2=Real.pi*x := by ring
  rw [ht,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

/-- The integer removed from the frequency changes no circle phase.
The identity uses the actual frequency c*t and its centered representative. -/
lemma actual_integer_frequency_phase (c a : ℤ) (t : ℝ) :
    fourier c (t : AddCircle (1 : ℝ))=
      fourier (1 : ℤ) ((c*t-(a : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  have ha : ((a : ℝ) : AddCircle (1 : ℝ))=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨a,by simp⟩
  have hx : ((c*t-(a : ℝ) : ℝ) : AddCircle (1 : ℝ))=
      c • (t : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub,ha,sub_zero]
    simpa only [zsmul_eq_mul] using
      (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := c) (x := t))
  simp only [fourier_apply,one_smul,hx]

/-- Reciprocal-distance estimate for a literal centered frequency.
Nonzero distance is explicit, so resonances cannot be divided away. -/
theorem actual_frequency_reciprocal_bound (c a : ℤ) (t : ℝ)
    (hx : |(c : ℝ)*t-(a : ℝ)|≤1/2) (hz : (c : ℝ)*t-(a : ℝ)≠0) :
    fourier c (t : AddCircle (1 : ℝ))≠1 ∧
      2/‖fourier c (t : AddCircle (1 : ℝ))-1‖≤
        1/(2*|(c : ℝ)*t-(a : ℝ)|) := by
  have hb := actual_centered_chord_lower ((c : ℝ)*t-(a : ℝ)) hx
  rw [←actual_integer_frequency_phase] at hb
  have hd : 0<|(c : ℝ)*t-(a : ℝ)| := abs_pos.mpr hz
  have hn : fourier c (t : AddCircle (1 : ℝ))≠1 := by
    intro he
    rw [he,sub_self,norm_zero] at hb
    linarith
  refine ⟨hn,?_⟩
  calc
    _ ≤ 2/(4*|(c : ℝ)*t-(a : ℝ)|) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hb
    _ = _ := by field_simp [ne_of_gt hd]; ring

/-- Weighted reciprocal-distance cancellation with the original finite
variation cost. No rational approximation existence or minor-domain
separation is asserted or hidden in this statement. -/
theorem actual_weighted_reciprocal_distance (c a : ℤ) (t : ℝ)
    (g : ℕ → ℂ) (N : ℕ) (hx : |(c : ℝ)*t-(a : ℝ)|≤1/2)
    (hz : (c : ℝ)*t-(a : ℝ)≠0) :
    ‖weightedLinearInterval c 0 g (N+1) (t : AddCircle (1 : ℝ))‖≤
      min ((N : ℝ)+1) (1/(2*|(c : ℝ)*t-(a : ℝ)|))*variation g N := by
  obtain ⟨hn,hbound⟩ := actual_frequency_reciprocal_bound c a t hx hz
  apply (actual_weighted_linear_cancellation c 0 g N _ hn).trans
  exact mul_le_mul_of_nonneg_right (min_le_min le_rfl hbound) (variation_nonneg g N)

end ActualOriginalReciprocalDistance318
