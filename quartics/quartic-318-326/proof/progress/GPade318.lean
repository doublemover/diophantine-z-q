module
public import GTail318
public section
namespace GPade318
open Pade21Domains Pade21Accuracy JTail318 GTail318
variable (p : ℕ) [Fact p.Prime]

theorem pade_units (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    Padic.addValuation (QG w)=0 ∧ Padic.addValuation (-98/2535:ℚ_[p])=0 := by
  have h2 : Padic.addValuation (2:ℚ_[p])=0 := by simpa using nat_unit p 2 (by decide) (by omega)
  have h3 : Padic.addValuation (3:ℚ_[p])=0 := by simpa using nat_unit p 3 (by decide) (by omega)
  have h5 : Padic.addValuation (5:ℚ_[p])=0 := by simpa using nat_unit p 5 (by decide) (by omega)
  have h7 : Padic.addValuation (7:ℚ_[p])=0 := by simpa using nat_unit p 7 (by decide) (by omega)
  have h13 : Padic.addValuation (13:ℚ_[p])=0 := by simpa using nat_unit p 13 (by decide) (by omega)
  have hc : Padic.addValuation (7/13:ℚ_[p])=0 := by
    rw [Padic.addValuation.map_div,h7,h13]
    simp
  have hv : Padic.addValuation ((7/13)*w)=((4*r:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.map_mul,hc,zero_add,
      Padic.addValuation.apply (HTail318.argument_ne_zero p w r hr hw),hw]
  have hq : Padic.addValuation (QG w)=0 := by
    change Padic.addValuation (1-(7/13)*w)=0
    have hh : Padic.addValuation (1:ℚ_[p])<Padic.addValuation ((7/13)*w) := by
      rw [Padic.addValuation.map_one,hv]
      exact_mod_cast (show (0:ℤ)<4*r by omega)
    exact (Padic.addValuation.map_sub_eq_of_lt_left hh).trans Padic.addValuation.map_one
  have h98 : Padic.addValuation (98:ℚ_[p])=0 := by
    rw [show (98:ℚ_[p])=2*7^2 by norm_num,Padic.addValuation.map_mul,
      Padic.addValuation.map_pow,h2,h7]
    simp
  have h2535 : Padic.addValuation (2535:ℚ_[p])=0 := by
    rw [show (2535:ℚ_[p])=3*5*13^2 by norm_num,Padic.addValuation.map_mul,
      Padic.addValuation.map_mul,Padic.addValuation.map_pow,h3,h5,h13]
    simp
  refine ⟨hq,?_⟩
  rw [Padic.addValuation.map_div,Padic.addValuation.map_neg,h98,h2535]
  simp

theorem finite_error_valuation (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    Padic.addValuation (PG w/QG w-G3 w)=((16*r:ℤ):WithTop ℤ) := by
  obtain ⟨hQ,hC⟩ := pade_units p hp w r hr hw
  rw [Pade21LocalError.G_error_valuation Padic.addValuation w hQ hC,
    Padic.addValuation.apply (HTail318.argument_ne_zero p w r hr hw),hw]
  exact_mod_cast (show (4:ℕ) • (4*r:ℤ)=16*r by simp only [nsmul_eq_mul]; ring)

/-- Full actual G-factor Padé precision on the chosen near-1 square-root branch.
The separate elliptic-log identification, homomorphism and isometry are not assumed. -/
theorem full_G_pade_precision (hp : 19≤p) (v w : ℚ_[p]) (hc : v^2=1-w)
    (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (G p v w-PG w/QG w) := by
  have hw : w.valuation=4*r := by
    rw [curve_substitution p v w hc]
    exact substitution_valuation p hp (v-1) r hr hd
  have htail := full_G_tail_precision p hp v w hc r hr hd
  have hfinite : ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (PG w/QG w-G3 w) := by
    rw [finite_error_valuation p hp w r hr hw]
  have hh := Padic.addValuation.map_le_sub htail hfinite
  convert hh using 1 <;> congr 1 <;> ring

end GPade318
#print axioms GPade318.full_G_pade_precision
