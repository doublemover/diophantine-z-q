module
public import JTail318
public section
namespace JPade318
open Pade21Domains Pade21Accuracy JTail318
variable (p : ℕ) [Fact p.Prime]

theorem pade_units (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    Padic.addValuation (QJ d)=0 ∧ Padic.addValuation (5/507:ℚ_[p])=0 := by
  have h3 : Padic.addValuation (3:ℚ_[p])=0 := by
    simpa using nat_unit p 3 (by decide) (by omega)
  have h5 : Padic.addValuation (5:ℚ_[p])=0 := by
    simpa using nat_unit p 5 (by decide) (by omega)
  have h13 : Padic.addValuation (13:ℚ_[p])=0 := by
    simpa using nat_unit p 13 (by decide) (by omega)
  have hc : Padic.addValuation (5/13:ℚ_[p])=0 := by
    rw [Padic.addValuation.map_div,h5,h13]
    simp
  have hv : Padic.addValuation ((5/13)*d)=((4*r:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.map_mul,hc,zero_add,
      Padic.addValuation.apply (HTail318.argument_ne_zero p d r hr hd),hd]
  have hq : Padic.addValuation (QJ d)=0 := by
    change Padic.addValuation (1+(5/13)*d)=0
    have hh : Padic.addValuation (1:ℚ_[p])<Padic.addValuation ((5/13)*d) := by
      rw [Padic.addValuation.map_one,hv]
      exact_mod_cast (show (0:ℤ)<4*r by omega)
    exact (Padic.addValuation.map_add_eq_of_lt_left hh).trans Padic.addValuation.map_one
  have h507 : Padic.addValuation (507:ℚ_[p])=0 := by
    rw [show (507:ℚ_[p])=3*13^2 by norm_num,Padic.addValuation.map_mul,
      Padic.addValuation.map_pow,h3,h13]
    simp
  refine ⟨hq,?_⟩
  rw [Padic.addValuation.map_div,h5,h507]
  simp

theorem finite_error_valuation (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    Padic.addValuation (PJ d/QJ d-J3 d)=((16*r:ℤ):WithTop ℤ) := by
  obtain ⟨hQ,hC⟩ := pade_units p hp d r hr hd
  rw [Pade21LocalError.J_error_valuation Padic.addValuation d hQ hC,
    Padic.addValuation.apply (HTail318.argument_ne_zero p d r hr hd),hd]
  exact_mod_cast (show (4:ℕ) • (4*r:ℤ)=16*r by simp only [nsmul_eq_mul]; ring)

/-- The direct J factor is an actual convergent composition of H. -/
theorem actual_J_hasSum (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    HasSum (HTail318.term p (-2*d-d^2)) (J p d) :=
  HTail318.series_hasSum p hp (-2*d-d^2) r hr (substitution_valuation p hp d r hr hd)

/-- Full 16r Padé precision for actual J, not merely its finite cubic surrogate.
This theorem makes no assertion identifying J with an elliptic-group logarithm. -/
theorem full_J_pade_precision (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (J p d-PJ d/QJ d) := by
  have htail := full_J_tail_precision p hp d r hr hd
  have hfinite : ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (PJ d/QJ d-J3 d) := by
    rw [finite_error_valuation p hp d r hr hd]
  have hh := Padic.addValuation.map_le_sub htail hfinite
  convert hh using 1 <;> congr 1 <;> ring

end JPade318
#print axioms JPade318.actual_J_hasSum
#print axioms JPade318.full_J_pade_precision
