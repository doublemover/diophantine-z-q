module
public import GPade318
public section
namespace SeriesEndpoints318
open Pade21Accuracy Pade21Domains
variable (p : ℕ) [Fact p.Prime]

theorem term_zero : HTail318.term p 0 = fun j => if j=0 then 1 else 0 := by
  funext j
  cases j with
  | zero => norm_num [HTail318.term,HCoefficients318.coefficient]
  | succ j => simp [HTail318.term]

theorem H_zero : HTail318.H p 0=1 := by
  simp [HTail318.H,term_zero p]

theorem H_hasSum_zero : HasSum (HTail318.term p 0) 1 := by
  rw [term_zero]
  exact hasSum_ite_eq 0 1

theorem H_cubic_zero : HTail318.cubic p 0=1 := by
  rw [HCubic318.cubic_formula]
  norm_num

theorem J_zero : JTail318.J p 0=1 := by simp [JTail318.J,H_zero p]
theorem G_zero : GTail318.G p 1 0=1 := by simp [GTail318.G,H_zero p]

theorem J_pade_zero : JTail318.J p 0=PJ (0:ℚ_[p])/QJ 0 := by
  simp [J_zero p,PJ,QJ]

theorem G_pade_zero : GTail318.G p 1 0=PG (0:ℚ_[p])/QG 0 := by
  simp [G_zero p,PG,QG]

theorem H_zero_error_top : Padic.addValuation (HTail318.H p 0-HTail318.cubic p 0)=⊤ := by
  rw [H_zero,H_cubic_zero,sub_self,Padic.addValuation.map_zero]

theorem J_zero_error_top : Padic.addValuation (JTail318.J p 0-PJ (0:ℚ_[p])/QJ 0)=⊤ := by
  rw [J_pade_zero,sub_self,Padic.addValuation.map_zero]

theorem G_zero_error_top : Padic.addValuation (GTail318.G p 1 0-PG (0:ℚ_[p])/QG 0)=⊤ := by
  rw [G_pade_zero,sub_self,Padic.addValuation.map_zero]

/-- The zero endpoint is separated from a finite positive valuation hypothesis. -/
theorem H_precision_zero_or_finite (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (HTail318.H p w-HTail318.cubic p w) := by
  rcases hw with rfl|hw
  · rw [H_zero_error_top]
    exact le_top
  · exact HTail318.full_H_tail_precision p hp w r hr hw

theorem J_precision_zero_or_finite (hp : 19≤p) (d : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hd : d=0 ∨ d.valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (JTail318.J p d-PJ d/QJ d) := by
  rcases hd with rfl|hd
  · rw [J_zero_error_top]
    exact le_top
  · exact JPade318.full_J_pade_precision p hp d r hr hd

theorem G_precision_zero_or_finite (hp : 19≤p) (v w : ℚ_[p]) (hc : v^2=1-w)
    (r : ℤ) (hr : 1≤r) (hd : v-1=0 ∨ (v-1).valuation=4*r) :
    ((16*r:ℤ):WithTop ℤ)≤Padic.addValuation (GTail318.G p v w-PG w/QG w) := by
  rcases hd with hd|hd
  · have hv : v=1 := sub_eq_zero.mp hd
    subst v
    have hw : w=0 := by linear_combination hc
    subst w
    rw [G_zero_error_top]
    exact le_top
  · exact GPade318.full_G_pade_precision p hp v w hc r hr hd

end SeriesEndpoints318
#print axioms SeriesEndpoints318.H_hasSum_zero
#print axioms SeriesEndpoints318.J_precision_zero_or_finite
#print axioms SeriesEndpoints318.G_precision_zero_or_finite
