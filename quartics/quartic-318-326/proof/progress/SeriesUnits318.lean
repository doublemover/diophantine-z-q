module
public import SeriesEndpoints318
public section
namespace SeriesUnits318
open JTail318
variable (p : ℕ) [Fact p.Prime]

theorem cubic_error (w : ℚ_[p]) :
    HTail318.cubic p w-1 = w*(312+130*w+75*w^2)/3120 := by
  rw [HCubic318.cubic_formula]
  norm_num
  ring

theorem cubic_error_norm (hp : 19≤p) (w : ℚ_[p]) (hw : ‖w‖≤1) :
    ‖HTail318.cubic p w-1‖≤‖w‖ := by
  have h2 : ‖(2:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 2 (by decide) (by omega)
  have h3 : ‖(3:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 3 (by decide) (by omega)
  have h5 : ‖(5:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 5 (by decide) (by omega)
  have h13 : ‖(13:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 13 (by decide) (by omega)
  have hn : ‖(3120:ℚ_[p])‖=1 := by
    rw [show (3120:ℚ_[p])=2^4*3*5*13 by norm_num]
    simp only [norm_mul,norm_pow,h2,h3,h5,h13]
    norm_num
  have hw2 : ‖w^2‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  have hpoly : ‖(312:ℚ_[p])+130*w+75*w^2‖≤1 :=
    norm_add_le_one p _ _
      (norm_add_le_one p _ _ (norm_nat_le_one p 312)
        (norm_mul_le_one p _ _ (norm_nat_le_one p 130) hw))
      (norm_mul_le_one p _ _ (norm_nat_le_one p 75) hw2)
  rw [cubic_error,norm_div,norm_mul,hn,div_one]
  exact (mul_le_mul_of_nonneg_left hpoly (norm_nonneg w)).trans_eq (mul_one _)

theorem H_relative_precision (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) :
    ((4*r:ℤ):WithTop ℤ)≤Padic.addValuation (HTail318.H p w-1) := by
  have hC : ((4*r:ℤ):WithTop ℤ)≤Padic.addValuation (HTail318.cubic p w-1) := by
    apply (HTail318.norm_le_iff_valuation p _ (4*r)).mp
    have hn : ‖w‖=(p:ℝ)^(-(4*r)) := by
      rw [Padic.norm_eq_zpow_neg_valuation (HTail318.argument_ne_zero p w r hr hw),hw]
    exact (cubic_error_norm p hp w (norm_small_argument p w r hr hw)).trans_eq hn
  have hT := HTail318.full_H_tail_precision p hp w r hr hw
  have hstep : ((4*r:ℤ):WithTop ℤ)≤((16*r:ℤ):WithTop ℤ) := by
    exact_mod_cast (show 4*r≤16*r by omega)
  have hh := Padic.addValuation.map_le_add (hstep.trans hT) hC
  simpa only [sub_add_sub_cancel] using hh

theorem H_unit (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w.valuation=4*r) : Padic.addValuation (HTail318.H p w)=0 := by
  have hpos : (0:WithTop ℤ)<((4*r:ℤ):WithTop ℤ) := by
    exact_mod_cast (show (0:ℤ)<4*r by omega)
  have hh : Padic.addValuation (1:ℚ_[p])<Padic.addValuation (HTail318.H p w-1) := by
    rw [Padic.addValuation.map_one]
    exact hpos.trans_le (H_relative_precision p hp w r hr hw)
  have he := Padic.addValuation.map_add_eq_of_lt_left hh
  simpa only [add_sub_cancel,Padic.addValuation.map_one] using he

theorem H_unit_zero_or_finite (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) : Padic.addValuation (HTail318.H p w)=0 := by
  rcases hw with rfl|hw
  · rw [SeriesEndpoints318.H_zero,Padic.addValuation.map_one]
  · exact H_unit p hp w r hr hw

theorem G_relative_precision (hp : 19≤p) (v w : ℚ_[p]) (hc : v^2=1-w)
    (r : ℤ) (hr : 1≤r) (hd : (v-1).valuation=4*r) :
    ((4*r:ℤ):WithTop ℤ)≤Padic.addValuation (GTail318.G p v w-1) := by
  have hw : w.valuation=4*r := by
    rw [GTail318.curve_substitution p v w hc]
    exact substitution_valuation p hp (v-1) r hr hd
  have hm : ((4*r:ℤ):WithTop ℤ)≤Padic.addValuation ((v-1)*HTail318.H p w) := by
    rw [Padic.addValuation.map_mul,H_unit p hp w r hr hw,add_zero,
      Padic.addValuation.apply (HTail318.argument_ne_zero p (v-1) r hr hd),hd]
  have hh := Padic.addValuation.map_le_add hm (H_relative_precision p hp w r hr hw)
  convert hh using 1 <;> simp only [GTail318.G] <;> congr 1 <;> ring

end SeriesUnits318
#print axioms SeriesUnits318.H_relative_precision
#print axioms SeriesUnits318.H_unit_zero_or_finite
#print axioms SeriesUnits318.G_relative_precision
