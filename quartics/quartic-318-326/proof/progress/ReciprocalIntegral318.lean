module
public import SeriesUnits318
public section
namespace ReciprocalIntegral318
variable (p : ℕ) [Fact p.Prime]

/-- The actual convergent reciprocal integral. Naming it does not assert a group law. -/
@[expose] noncomputable def integral (u w : ℚ_[p]) : ℚ_[p] := -u*HTail318.H p w
@[expose] noncomputable def parameter (u v : ℚ_[p]) : ℚ_[p] := -u/v

theorem integral_hasSum (hp : 19≤p) (u w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    HasSum (fun j => -u*HTail318.term p w j) (integral p u w) :=
  (HTail318.series_hasSum p hp w r hr hw).mul_left (-u)

theorem integral_zero (w : ℚ_[p]) : integral p 0 w=0 := by simp [integral]

theorem integral_valuation (hp : 19≤p) (u w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    Padic.addValuation (integral p u w)=Padic.addValuation u := by
  rw [integral,Padic.addValuation.map_mul,Padic.addValuation.map_neg,
    SeriesUnits318.H_unit_zero_or_finite p hp w r hr hw,add_zero]

theorem integral_eq_zero_iff (hp : 19≤p) (u w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) : integral p u w=0 ↔ u=0 := by
  rw [←Padic.addValuation.top_iff,integral_valuation p hp u w r hr hw,
    Padic.addValuation.top_iff]

theorem branch_unit (v : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : (v-1).valuation=4*r) : Padic.addValuation v=0 := by
  have h := GTail318.one_add_unit p (v-1) r hr hd
  simpa only [add_sub_cancel] using h

theorem branch_ne_zero (v : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : (v-1).valuation=4*r) : v≠0 := by
  apply Padic.addValuation.ne_top_iff.mp
  rw [branch_unit p v r hr hd]
  exact WithTop.coe_ne_top

theorem integral_eq_parameter_factor (u v w : ℚ_[p]) (hv : v≠0) :
    integral p u w=parameter p u v*GTail318.G p v w := by
  simp only [integral,parameter,GTail318.G]
  field_simp

theorem parameter_valuation (u v : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : (v-1).valuation=4*r) :
    Padic.addValuation (parameter p u v)=Padic.addValuation u := by
  rw [parameter,Padic.addValuation.map_div,Padic.addValuation.map_neg,
    branch_unit p v r hr hd,sub_zero]

/-- Valuation preservation at the identity for the actual series, without assuming
it is the elliptic-group logarithm or a homomorphism. -/
theorem integral_parameter_valuation (hp : 19≤p) (u v w : ℚ_[p])
    (hc : v^2=1-w) (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    Padic.addValuation (integral p u w)=Padic.addValuation (parameter p u v) := by
  have hw : w.valuation=4*r := by
    rw [GTail318.curve_substitution p v w hc]
    exact JTail318.substitution_valuation p hp (v-1) r hr hd
  rw [parameter_valuation p u v r hr hd]
  exact integral_valuation p hp u w r hr (Or.inr hw)

theorem integral_parameter_error (hp : 19≤p) (u v w : ℚ_[p])
    (hc : v^2=1-w) (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    Padic.addValuation u+((4*r:ℤ):WithTop ℤ)≤
      Padic.addValuation (integral p u w-parameter p u v) := by
  rw [integral_eq_parameter_factor p u v w (branch_ne_zero p v r hr hd)]
  rw [show parameter p u v*GTail318.G p v w-parameter p u v=
    parameter p u v*(GTail318.G p v w-1) by ring]
  rw [Padic.addValuation.map_mul,parameter_valuation p u v r hr hd]
  exact add_le_add le_rfl (SeriesUnits318.G_relative_precision p hp v w hc r hr hd)

theorem integral_G_pade_error (hp : 19≤p) (u v w : ℚ_[p])
    (hc : v^2=1-w) (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    Padic.addValuation u+((16*r:ℤ):WithTop ℤ)≤
      Padic.addValuation (integral p u w-parameter p u v*
        (Pade21Domains.PG w/Pade21Domains.QG w)) := by
  rw [integral_eq_parameter_factor p u v w (branch_ne_zero p v r hr hd)]
  rw [show parameter p u v*GTail318.G p v w-parameter p u v*
    (Pade21Domains.PG w/Pade21Domains.QG w)=parameter p u v*
    (GTail318.G p v w-Pade21Domains.PG w/Pade21Domains.QG w) by ring]
  rw [Padic.addValuation.map_mul,parameter_valuation p u v r hr hd]
  exact add_le_add le_rfl (GPade318.full_G_pade_precision p hp v w hc r hr hd)

end ReciprocalIntegral318
#print axioms ReciprocalIntegral318.integral_hasSum
#print axioms ReciprocalIntegral318.integral_eq_zero_iff
#print axioms ReciprocalIntegral318.integral_parameter_valuation
#print axioms ReciprocalIntegral318.integral_parameter_error
#print axioms ReciprocalIntegral318.integral_G_pade_error
