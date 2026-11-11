module
public import CoherentMultipleCharts318
public section
noncomputable section
namespace CoherentOrbit318
open LocalGenerator318 (E P)
open GlobalGeneratorPoints318 (R double_R)
open WeierstrassCurve.Affine
set_option maxHeartbeats 1000000

lemma multiple_R_nonzero (n : ℤ) (hn : n≠0) : n • R≠0 := by
  intro hz
  apply RealMultiples318.multiple_P_nonzero n hn
  rw [←double_R,zsmul_add,hz,zero_add]

theorem half_orbit_injective : Function.Injective (fun n : ℤ => n • R) := by
  intro m n he
  change m • R=n • R at he
  by_contra hmn
  apply multiple_R_nonzero (m-n) (sub_ne_zero.mpr hmn)
  rw [sub_zsmul,he,add_neg_cancel]

lemma adjacent_distinct (n h : ℤ) (hn : n≠0) : (n*h) • R≠(n*(h-1)) • R := by
  intro he
  have hi := half_orbit_injective he
  have ht := mul_left_cancel₀ hn hi
  omega

lemma adjacent_not_negative (n h : ℤ) (hn : n≠0) : (n*h) • R≠ -((n*(h-1)) • R) := by
  intro he
  rw [←neg_zsmul] at he
  have hi := half_orbit_injective he
  have hz : n*(2*h-1)=0 := by linear_combination hi
  have hh : 2*h-1=0 := (mul_eq_zero.mp hz).resolve_left hn
  omega

/-- Adjacent half-orbit points never share an abscissa, even up to sign.
This removes every exceptional secant branch for nonzero source labels. -/
theorem adjacent_xRep_ne (n h : ℤ) (hn : n≠0) :
    ((n*h) • R).xRep≠((n*(h-1)) • R).xRep := by
  intro he
  rcases Point.eq_or_eq_neg_of_xRep_eq_xRep he with he|he
  · exact adjacent_distinct n h hn he
  · exact adjacent_not_negative n h hn he

end CoherentOrbit318
