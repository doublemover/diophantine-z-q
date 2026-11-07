module
public import JPade318
public section
namespace GTail318
open Pade21Accuracy Pade21Domains JTail318
variable (p : ℕ) [Fact p.Prime]
@[expose] noncomputable def G (v w : ℚ_[p]) : ℚ_[p] := v*HTail318.H p w
@[expose] noncomputable def Gd (d : ℚ_[p]) : ℚ_[p] := (1+d)*J p d

theorem one_add_unit (d : ℚ_[p]) (r : ℤ) (hr : 1≤r) (hd : d.valuation=4*r) :
    Padic.addValuation (1+d)=0 := by
  have hh : Padic.addValuation (1:ℚ_[p])<Padic.addValuation d := by
    rw [Padic.addValuation.map_one,Padic.addValuation.apply (HTail318.argument_ne_zero p d r hr hd),hd]
    exact_mod_cast (show (0:ℤ)<4*r by omega)
  exact (Padic.addValuation.map_add_eq_of_lt_left hh).trans Padic.addValuation.map_one

theorem composition_error (d : ℚ_[p]) :
    (1+d)*J3 d-G3 (-2*d-d^2)=-(d^4*(147+84*d+14*d^2))/195 := by
  norm_num [J3,G3]
  ring

theorem composition_error_norm (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    ‖(1+d)*J3 d-G3 (-2*d-d^2)‖≤(p:ℝ)^(-(16*r)) := by
  have hd1 := norm_small_argument p d r hr hd
  have hd2 : ‖d^2‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg d) hd1
  have hpoly : ‖(147:ℚ_[p])+84*d+14*d^2‖≤1 :=
    norm_add_le_one p _ _
      (norm_add_le_one p _ _ (norm_nat_le_one p 147)
        (norm_mul_le_one p _ _ (norm_nat_le_one p 84) hd1))
      (norm_mul_le_one p _ _ (norm_nat_le_one p 14) hd2)
  have hn3 : ‖(3:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 3 (by decide) (by omega)
  have hn5 : ‖(5:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 5 (by decide) (by omega)
  have hn13 : ‖(13:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 13 (by decide) (by omega)
  have hn : ‖(195:ℚ_[p])‖=1 := by
    rw [show (195:ℚ_[p])=3*5*13 by norm_num,norm_mul,norm_mul,hn3,hn5,hn13]
    norm_num
  rw [composition_error p d,norm_div,norm_neg,norm_mul,norm_pow,hn,div_one]
  calc
    ‖d‖^4*‖(147:ℚ_[p])+84*d+14*d^2‖ ≤ ‖d‖^4*1 :=
      mul_le_mul_of_nonneg_left hpoly (pow_nonneg (norm_nonneg d) _)
    _ = (p:ℝ)^(-(16*r)) := by rw [mul_one,norm_four p d r hr hd]

theorem full_Gd_tail_precision (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (Gd p d-G3 (-2*d-d^2)) := by
  have hJ := full_J_tail_precision p hp d r hr hd
  have hm : ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation ((1+d)*(J p d-J3 d)) := by
    rw [Padic.addValuation.map_mul,one_add_unit p d r hr hd,zero_add]
    exact hJ
  have hc := (HTail318.norm_le_iff_valuation p _ (16*r)).mp
    (composition_error_norm p hp d r hr hd)
  have hh := Padic.addValuation.map_le_add hm hc
  convert hh using 1 <;> simp only [Gd] <;> congr 1 <;> ring

theorem curve_substitution (v w : ℚ_[p]) (hc : v^2=1-w) :
    w=-2*(v-1)-(v-1)^2 := by
  calc
    w=1-v^2 := by linear_combination hc
    _ = -2*(v-1)-(v-1)^2 := by ring

theorem actual_G_hasSum (hp : 19≤p) (v w : ℚ_[p]) (hc : v^2=1-w)
    (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    HasSum (fun j => v*HTail318.term p w j) (G p v w) := by
  have hw : w.valuation=4*r := by
    rw [curve_substitution p v w hc]
    exact substitution_valuation p hp (v-1) r hr hd
  exact (HTail318.series_hasSum p hp w r hr hw).mul_left v

/-- The chosen algebraic branch v²=1−w with v−1 of positive depth.
No elliptic logarithm identification is asserted. -/
theorem full_G_tail_precision (hp : 19≤p) (v w : ℚ_[p]) (hc : v^2=1-w)
    (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (G p v w-G3 w) := by
  rw [curve_substitution p v w hc]
  have hh := full_Gd_tail_precision p hp (v-1) r hr hd
  simpa only [G,Gd,J,add_sub_cancel] using hh

end GTail318
#print axioms GTail318.actual_G_hasSum
#print axioms GTail318.full_G_tail_precision
