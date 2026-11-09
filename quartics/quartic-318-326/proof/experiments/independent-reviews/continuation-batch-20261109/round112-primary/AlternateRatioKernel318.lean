module
public import ActualJLog318
public import ActualLogRatio318
public section
namespace AlternateRatioKernel318
open Pade21Domains ActualLogRatio318 CanonicalRoot318
variable (p:ℕ) [Fact p.Prime]
noncomputable section
set_option maxHeartbeats 0

@[expose] def approximation (full:Bool) (d:ℚ_[p]) : ℚ_[p] :=
  if full then PJ d/QJ d else 1-d/5
@[expose] def rate (full:Bool) : ℤ := if full then 16 else 8

theorem J_unit (hp:19≤p) (d:ℚ_[p]) (r:ℤ) (hr:1≤r)
    (hd:d=0 ∨ d.valuation=4*r) : Padic.addValuation (JTail318.J p d)=0 := by
  rcases hd with rfl|hd
  · rw [SeriesEndpoints318.J_zero,Padic.addValuation.map_one]
  · exact SeriesUnits318.H_unit p hp _ r hr (JTail318.substitution_valuation p hp d r hr hd)

theorem approximation_error (hp:19≤p) (full:Bool) (d:ℚ_[p]) (r:ℤ) (hr:1≤r)
    (hd:d=0 ∨ d.valuation=4*r) :
    ((rate full*r:ℤ):WithTop ℤ)≤Padic.addValuation (JTail318.J p d-approximation p full d) := by
  cases full
  · exact JLinear318.full_J_linear_precision p hp d r hr hd
  · exact SeriesEndpoints318.J_precision_zero_or_finite p hp d r hr hd

theorem approximation_unit (hp:19≤p) (full:Bool) (d:ℚ_[p]) (r:ℤ) (hr:1≤r)
    (hd:d=0 ∨ d.valuation=4*r) : Padic.addValuation (approximation p full d)=0 := by
  apply approximate_unit Padic.addValuation (JTail318.J p d) _ (J_unit p hp d r hr hd)
  apply lt_of_lt_of_le _ (approximation_error p hp full d r hr hd)
  have hpos:0<rate full*r := by cases full <;> simp only [rate,Bool.false_eq_true,ite_false,ite_true] <;> omega
  exact_mod_cast hpos

/-- The mixed J/G quotient keeps the numerator's correct linear/Padé rate
and the denominator's order16 rate, including a zero numerator. -/
theorem mixed_ratio_precision (hp:19≤p) (full:Bool) (u z d w:ℚ_[p])
    (r s:ℤ) (hr:1≤r) (hs:1≤s)
    (hd:d=0 ∨ d.valuation=4*r) (hw:w=0 ∨ w.valuation=4*s) :
    Padic.addValuation (u/z)+((min (rate full*r) (16*s):ℤ):WithTop ℤ)≤
      Padic.addValuation ((-u*JTail318.J p d)/(z*factor p hp w)-
        (-u*approximation p full d)/(z*(PG w/QG w))) := by
  let k:WithTop ℤ:=(min (rate full*r) (16*s):ℤ)
  have hkr:k≤((rate full*r:ℤ):WithTop ℤ) := WithTop.coe_le_coe.mpr (min_le_left (rate full*r) (16*s))
  have hks:k≤((16*s:ℤ):WithTop ℤ) := WithTop.coe_le_coe.mpr (min_le_right (rate full*r) (16*s))
  have he:=ratio_error Padic.addValuation (JTail318.J p d) (factor p hp w)
    (approximation p full d) (PG w/QG w) k (factor_unit p hp w s hs hw)
    (approximation_unit p hp full d r hr hd) (pade_factor_unit p hp w s hs hw)
    (hkr.trans (approximation_error p hp full d r hr hd))
    (hks.trans (factor_pade_precision p hp w s hs hw))
  rw [←div_mul_div_comm,←div_mul_div_comm,←mul_sub,Padic.addValuation.map_mul]
  simp only [Padic.addValuation.map_div,Padic.addValuation.map_neg]
  simpa only [Padic.addValuation.map_div] using add_le_add (le_refl (Padic.addValuation (u/z))) he

end
end AlternateRatioKernel318
#print axioms AlternateRatioKernel318.mixed_ratio_precision
