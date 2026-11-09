module
public import CanonicalRoot318
public section
namespace JLinear318
open JTail318 Pade21Accuracy
variable (p : ℕ) [Fact p.Prime]

theorem cubic_linear_error (d : ℚ_[p]) : J3 d-(1-d/5)=d^2*(13-5*d)/195 := by
  norm_num [J3]
  ring

theorem cubic_linear_norm (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) : ‖J3 d-(1-d/5)‖≤(p:ℝ)^(-(8*r)) := by
  have h3 : ‖(3:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 3 (by decide) (by omega)
  have h5 : ‖(5:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 5 (by decide) (by omega)
  have h13 : ‖(13:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 13 (by decide) (by omega)
  have hn : ‖(195:ℚ_[p])‖=1 := by
    rw [show (195:ℚ_[p])=3*5*13 by norm_num,norm_mul,norm_mul,h3,h5,h13]
    norm_num
  have hpoly : ‖(13:ℚ_[p])-5*d‖≤1 := by
    rw [sub_eq_add_neg]
    apply norm_add_le_one p _ _ h13.le
    rw [norm_neg]
    exact norm_mul_le_one p _ _ h5.le (norm_small_argument p d r hr hd)
  have hd2 : ‖d‖^2=(p:ℝ)^(-(8*r)) := by
    rw [Padic.norm_eq_zpow_neg_valuation (HTail318.argument_ne_zero p d r hr hd),hd,
      ←zpow_natCast,←zpow_mul]
    congr 1
    ring
  rw [cubic_linear_error,norm_div,norm_mul,norm_pow,hn,div_one]
  exact (mul_le_mul_of_nonneg_left hpoly (pow_nonneg (norm_nonneg d) _)).trans_eq
    (by rw [mul_one,hd2])

theorem full_J_linear_precision (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d=0 ∨ d.valuation=4*r) :
    ((8*r:ℤ):WithTop ℤ)≤Padic.addValuation (J p d-(1-d/5)) := by
  rcases hd with rfl|hd
  · simp [SeriesEndpoints318.J_zero]
  · have hT := full_J_tail_precision p hp d r hr hd
    have hstep : ((8*r:ℤ):WithTop ℤ)≤((16*r:ℤ):WithTop ℤ) := by
      exact_mod_cast (show 8*r≤16*r by omega)
    have hC := (HTail318.norm_le_iff_valuation p _ (8*r)).mp (cubic_linear_norm p hp d r hr hd)
    have hh := Padic.addValuation.map_le_add (hstep.trans hT) hC
    simpa only [sub_add_sub_cancel] using hh
end JLinear318
#print axioms JLinear318.full_J_linear_precision
