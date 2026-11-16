module
public import ActualOriginalCanonicalSliceCancellation318
public import Mathlib.RingTheory.Coprime.Basic
public section
noncomputable section
namespace ActualOriginalRationalDistanceSeparation318

/-- Nonzero integer determinant is the arithmetic source of separation.
The approximation error is multiplied by the ACTUAL frequency, explicitly. -/
theorem actual_integer_determinant_separation (a q c m : ℤ) (t : ℝ)
    (hq : 0<q) (hd : c*a-m*q≠0)
    (he : |(c : ℝ)|*|(q : ℝ)*t-(a : ℝ)|≤1/2) :
    1/(2*(q : ℝ))≤|(c : ℝ)*t-(m : ℝ)| := by
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hi : (1 : ℤ)≤|c*a-m*q| := by omega
  have hi' : (1 : ℝ)≤|(c : ℝ)*a-(m : ℝ)*q| := by exact_mod_cast hi
  have hid : (q : ℝ)*((c : ℝ)*t-m)-(c : ℝ)*((q : ℝ)*t-a)=
      (c : ℝ)*a-(m : ℝ)*q := by ring
  have ht := abs_sub ((q : ℝ)*((c : ℝ)*t-m)) ((c : ℝ)*((q : ℝ)*t-a))
  rw [hid,abs_mul,abs_mul,abs_of_pos hqi] at ht
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*q)).mpr
  nlinarith

lemma actual_coprime_determinant_nonzero (a q c m : ℤ)
    (ha : IsCoprime q a) (hc : ¬q∣c) : c*a-m*q≠0 := by
  intro h
  apply hc
  apply ha.dvd_of_dvd_mul_right
  exact ⟨m,by nlinarith⟩

/-- The approximation |t-a/q|<=q^-2 gives the needed scaled error
on the entire frequency block |c|<=q/2. No approximation existence is claimed. -/
lemma actual_rational_block_error (a q c : ℤ) (t : ℝ) (hq : 0<q)
    (ha : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (hc : |(c : ℝ)|≤(q : ℝ)/2) :
    |(c : ℝ)|*|(q : ℝ)*t-(a : ℝ)|≤1/2 := by
  have hqi : (0 : ℝ)<q := by exact_mod_cast hq
  have hqn : (q : ℝ)≠0 := ne_of_gt hqi
  have hid : (q : ℝ)*t-a=(q : ℝ)*(t-(a : ℝ)/q) := by field_simp; ring
  have he : |(q : ℝ)*t-a|≤1/(q : ℝ) := by
    rw [hid,abs_mul,abs_of_pos hqi]
    calc
      _ ≤ (q : ℝ)*(1/(q : ℝ)^2) := mul_le_mul_of_nonneg_left ha (le_of_lt hqi)
      _ = _ := by field_simp; ring
  calc
    _ ≤ ((q : ℝ)/2)*(1/(q : ℝ)) :=
      mul_le_mul hc he (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

/-- Coprimality discharges the determinant condition for EVERY integer
m and every nonmultiple frequency in the controlled block. -/
theorem actual_rational_block_separation (a q c : ℤ) (t : ℝ) (hq : 0<q)
    (ha : IsCoprime q a) (hc : ¬q∣c)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2)
    (hsize : |(c : ℝ)|≤(q : ℝ)/2) (m : ℤ) :
    1/(2*(q : ℝ))≤|(c : ℝ)*t-(m : ℝ)| :=
  actual_integer_determinant_separation a q c m t hq
    (actual_coprime_determinant_nonzero a q c m ha hc)
    (actual_rational_block_error a q c t hq ht hsize)

end ActualOriginalRationalDistanceSeparation318
