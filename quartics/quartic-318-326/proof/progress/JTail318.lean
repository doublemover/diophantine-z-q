module
public import HCubic318
public import Pade21LocalError
public section
namespace JTail318
open Pade21Accuracy Pade21Domains
variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def J (d : ℚ_[p]) : ℚ_[p] := HTail318.H p (-2*d-d^2)

theorem nat_unit (n : ℕ) (hn : 0<n) (hnp : n<p) :
    Padic.addValuation (n:ℚ_[p])=0 := by
  have hnot : ¬p∣n := fun h => (not_le_of_gt hnp) (Nat.le_of_dvd hn h)
  rw [Padic.addValuation.apply (by exact_mod_cast (Nat.ne_of_gt hn)),
    Padic.valuation_natCast,padicValNat.eq_zero_of_not_dvd hnot]
  rfl

theorem norm_nat_unit (n : ℕ) (hn : 0<n) (hnp : n<p) : ‖(n:ℚ_[p])‖=1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => (not_le_of_gt hnp) (Nat.le_of_dvd hn h))

theorem norm_nat_le_one (n : ℕ) : ‖(n:ℚ_[p])‖≤1 := by
  simpa only [Int.cast_natCast] using (Padic.norm_int_le_one (p:=p) (n:ℤ))

theorem substitution_valuation (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) : (-2*d-d^2).valuation=4*r := by
  have hd0 := HTail318.argument_ne_zero p d r hr hd
  have hdv : Padic.addValuation d=((4*r:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.apply hd0,hd]
  have h2 : Padic.addValuation (2:ℚ_[p])=0 := by
    simpa using nat_unit p 2 (by decide) (by omega)
  have hlt : Padic.addValuation (2:ℚ_[p])<Padic.addValuation d := by
    rw [h2,hdv]
    exact_mod_cast (show (0:ℤ)<4*r by omega)
  have hs : Padic.addValuation (2+d)=0 :=
    (Padic.addValuation.map_add_eq_of_lt_left hlt).trans h2
  have he : -2*d-d^2=(-d)*(2+d) := by ring
  have hv : Padic.addValuation (-2*d-d^2)=((4*r:ℤ):WithTop ℤ) := by
    rw [he,Padic.addValuation.map_mul,Padic.addValuation.map_neg,hs,add_zero,hdv]
  have hn : -2*d-d^2≠0 := Padic.addValuation.ne_top_iff.mp (by rw [hv]; exact WithTop.coe_ne_top)
  rw [Padic.addValuation.apply hn] at hv
  exact_mod_cast hv

theorem composition_error (d : ℚ_[p]) :
    HTail318.cubic p (-2*d-d^2)-J3 d = -(d^4*(154+90*d+15*d^2))/624 := by
  rw [HCubic318.cubic_formula]
  norm_num [J3]
  ring

theorem norm_small_argument (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) : ‖d‖≤1 := by
  have hd0 := HTail318.argument_ne_zero p d r hr hd
  have hpos : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hd0,hd]
  exact (zpow_le_zpow_right₀ hpos.le (show -(4*r)≤0 by omega)).trans_eq (zpow_zero _)

theorem norm_four (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) : ‖d‖^4=(p:ℝ)^(-(16*r)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (HTail318.argument_ne_zero p d r hr hd),hd,
    ←zpow_natCast,←zpow_mul]
  congr 1
  ring

theorem norm_add_le_one (x y : ℚ_[p]) (hx : ‖x‖≤1) (hy : ‖y‖≤1) : ‖x+y‖≤1 :=
  (Padic.nonarchimedean x y).trans (max_le hx hy)

theorem norm_mul_le_one (x y : ℚ_[p]) (hx : ‖x‖≤1) (hy : ‖y‖≤1) : ‖x*y‖≤1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg x,norm_nonneg y]

theorem composition_error_norm (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    ‖HTail318.cubic p (-2*d-d^2)-J3 d‖≤(p:ℝ)^(-(16*r)) := by
  have hd1 := norm_small_argument p d r hr hd
  have hd2 : ‖d^2‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg d) hd1
  have hpoly : ‖(154:ℚ_[p])+90*d+15*d^2‖≤1 :=
    norm_add_le_one p _ _
      (norm_add_le_one p _ _ (norm_nat_le_one p 154)
        (norm_mul_le_one p _ _ (norm_nat_le_one p 90) hd1))
      (norm_mul_le_one p _ _ (norm_nat_le_one p 15) hd2)
  have hn2 : ‖(2:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 2 (by decide) (by omega)
  have hn3 : ‖(3:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 3 (by decide) (by omega)
  have hn13 : ‖(13:ℚ_[p])‖=1 := by simpa using norm_nat_unit p 13 (by decide) (by omega)
  have hn : ‖(624:ℚ_[p])‖=1 := by
    rw [show (624:ℚ_[p])=2^4*3*13 by norm_num, norm_mul,norm_mul,norm_pow,
      hn2,hn3,hn13]
    norm_num
  rw [composition_error p d,norm_div,norm_neg,norm_mul,norm_pow,hn,div_one]
  calc
    ‖d‖^4*‖(154:ℚ_[p])+90*d+15*d^2‖ ≤ ‖d‖^4*1 :=
      mul_le_mul_of_nonneg_left hpoly (pow_nonneg (norm_nonneg d) _)
    _ = (p:ℝ)^(-(16*r)) := by rw [mul_one,norm_four p d r hr hd]

/-- Actual composition of the convergent H-series, rather than a finite surrogate. -/
theorem full_J_tail_precision (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (J p d-J3 d) := by
  have hw := substitution_valuation p hp d r hr hd
  have hH := HTail318.full_H_tail_precision p hp (-2*d-d^2) r hr hw
  have hc := (HTail318.norm_le_iff_valuation p _ (16*r)).mp
    (composition_error_norm p hp d r hr hd)
  have hh := Padic.addValuation.map_le_add hH hc
  convert hh using 1 <;> simp only [J] <;> congr 1 <;> ring

end JTail318
#print axioms JTail318.full_J_tail_precision
