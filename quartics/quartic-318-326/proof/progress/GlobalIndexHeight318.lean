module
public import GlobalTorsionOddIndex318
public import BasePointHeight318
public section
namespace GlobalIndexHeight318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalSaturationHeight318
set_option maxHeartbeats 0
noncomputable section

lemma base_canonical_lower {H:E.Point→ℝ} (d:CanonicalData H) : 1<2*H P := by
  have hh:=Real.log_lt_log (by norm_num : (0:ℝ)<2^6*392)
    (by norm_num : (2:ℝ)^6*392<41^3)
  rw [Real.log_mul (by positivity) (by norm_num),Real.log_pow,Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hl:=Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hl
  have hd:=d.lower P
  rw [d.heightP] at hd
  linarith

lemma upper_error_lt_six : Real.log (676:ℝ)/3<6 := by
  have hh:=Real.log_lt_log (by norm_num : (0:ℝ)<676) (by norm_num : (676:ℝ)<3^6)
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hl:=Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)≠1)
  linarith

/-- Actual absolute x-height grows at least quadratically in every integer
multiple of the displayed generator, with the explicit manuscript constant6. -/
theorem multiple_height_lower {H:E.Point→ℝ} (d:CanonicalData H) (n:ℤ) :
    (n:ℝ)^2-6<xHeight (n • P) := by
  have hp:=base_canonical_lower d
  have hu:=d.upper (n • P)
  rw [d.zsmul] at hu
  have hs:=mul_le_mul_of_nonneg_left hp.le (sq_nonneg (n:ℝ))
  nlinarith [upper_error_lt_six]

/-- The same estimate holds after the allowed common 2-torsion shift. -/
theorem coset_height_lower {H:E.Point→ℝ} (d:CanonicalData H)
    (n:ℤ) (U:E.Point) (hu:U+U=0) :
    (n:ℝ)^2-6<xHeight (n • P+U) := by
  have hp:=base_canonical_lower d
  have hh:=d.upper (n • P+U)
  rw [d.torsion _ _ hu,d.zsmul] at hh
  have hs:=mul_le_mul_of_nonneg_left hp.le (sq_nonneg (n:ℝ))
  nlinarith [upper_error_lt_six]

#print axioms multiple_height_lower
#print axioms coset_height_lower
end
end GlobalIndexHeight318
