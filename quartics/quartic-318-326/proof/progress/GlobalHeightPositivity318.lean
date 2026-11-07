module
public import GlobalSaturationHeight318
public section
namespace GlobalHeightPositivity318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalSaturationHeight318
set_option maxHeartbeats 0

/-- The stated canonical comparison already forces the actual generator's
height positive; no extra non-torsion/positivity assumption is needed. -/
theorem canonical_R_positive {H:E.Point→ℝ} (d:CanonicalData H) : 0<H R := by
  have hc:Real.log 392<3*Real.log 41 := by
    have hh:=Real.log_lt_log (by norm_num:(0:ℝ)<392) (by norm_num:(392:ℝ)<41^3)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlow:=d.lower P
  rw [d.heightP] at hlow
  have hP:H P=4*H R := by rw [←two_zsmul_R,d.zsmul]; norm_num
  rw [hP] at hlow
  linarith

end GlobalHeightPositivity318
#print axioms GlobalHeightPositivity318.canonical_R_positive
