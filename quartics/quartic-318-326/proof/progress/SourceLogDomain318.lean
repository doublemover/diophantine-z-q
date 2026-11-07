module
public import ActualLogIdentification318
public section
namespace SourceLogDomain318
open ActualLogHom318 ActualLogMembership318 ActualLogIdentification318
  ReciprocalDouble318 WeierstrassCurve.Affine
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- A directly usable valuation form of the actual affine logarithm domain. -/
theorem affine_mem_of_valuation (hp : 19≤p) (D x y : ℚ_[p])
    (hD : Padic.addValuation D=0) (hy : y≠0) (hc : y^2=x^3-D*x)
    (h : (E D).Nonsingular x y) (r : ℤ) (hr : 1≤r)
    (hx : Padic.addValuation x=((-2*r:ℤ):WithTop ℤ))
    (hz : (1:WithTop ℤ)≤Padic.addValuation (-x/y)) :
    ∃ hDn : ‖D‖≤1, Point.some x y h ∈ formalSubgroup p hp D hDn := by
  have hDn : ‖D‖≤1 := by
    simpa only [neg_zero,zpow_zero] using (HTail318.norm_le_iff_valuation p D 0).mpr (by rw [hD]; rfl)
  have hD0 : D≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hD]; simp)
  have hx0 : x≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hx]; exact WithTop.coe_ne_top)
  have hw0 : D/x^2≠0 := div_ne_zero hD0 (pow_ne_zero 2 hx0)
  have hwv : (D/x^2).valuation=4*r := by
    have he : Padic.addValuation (D/x^2)=((4*r:ℤ):WithTop ℤ) := by
      rw [Padic.addValuation.map_div,Padic.addValuation.map_pow,hD,hx]
      norm_cast
      norm_num [nsmul_eq_mul,Int.negSucc_eq] <;> ring
    rw [Padic.addValuation.apply hw0] at he
    exact WithTop.coe_inj.mp he
  have hzn : ‖-x/y‖≤‖(p:ℚ_[p])‖ := by
    have hh := (HTail318.norm_le_iff_valuation p (-x/y) 1).mpr hz
    simpa only [Padic.norm_p,zpow_neg_one] using hh
  exact ⟨hDn,affine_mem p hp D hDn x y hx0 hy hc h
    (CanonicalRoot318.argument_small p (D/x^2) r hr hwv) hzn⟩

/-- Every literal reciprocal chart of positive depth is in the actual log
subgroup, whether its supplied ordinate is near +1 or near -1, including O. -/
theorem reciprocal_mem_of_valuation (hp : 19≤p) (D u v : ℚ_[p])
    (hD : Padic.addValuation D=0) (hv : Padic.addValuation v=0)
    (hu : (1:WithTop ℤ)≤Padic.addValuation u) (hc : v^2=1-D*u^4) :
    ∃ (hDn : ‖D‖≤1) (hv0 : v≠0), point D u v hv0 hc ∈ formalSubgroup p hp D hDn := by
  have hv0 : v≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hv]; simp)
  have hDn : ‖D‖≤1 := by
    simpa only [neg_zero,zpow_zero] using (HTail318.norm_le_iff_valuation p D 0).mpr (by rw [hD]; rfl)
  by_cases hu0 : u=0
  · refine ⟨hDn,hv0,?_⟩
    subst u
    rw [point_zero]
    exact (formalSubgroup p hp D hDn).zero_mem
  obtain ⟨r,hrv⟩:=WithTop.ne_top_iff_exists.mp ((Padic.addValuation.ne_top_iff).mpr hu0)
  have hr : 1≤r := by rw [←hrv] at hu; exact_mod_cast hu
  have hx : Padic.addValuation (1/u^2)=((-2*r:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.map_div,Padic.addValuation.map_one,Padic.addValuation.map_pow,←hrv]
    norm_cast
    norm_num [nsmul_eq_mul,Int.negSucc_eq] <;> ring
  have hz : (1:WithTop ℤ)≤Padic.addValuation (-(1/u^2)/(v/u^3)) := by
    have he : -(1/u^2)/(v/u^3)= -u/v := by field_simp [hu0,hv0]
    rw [he,Padic.addValuation.map_div,Padic.addValuation.map_neg,hv,sub_zero]
    exact hu
  have hec : (v/u^3)^2=(1/u^2)^3-D*(1/u^2) := by
    field_simp [hu0]
    linear_combination hc
  obtain ⟨hDn',hm⟩:=affine_mem_of_valuation p hp D (1/u^2) (v/u^3) hD
    (div_ne_zero hv0 (pow_ne_zero 3 hu0)) hec (reciprocal_nonsingular D u v hu0 hv0 hc) r hr hx hz
  refine ⟨hDn',hv0,?_⟩
  simpa only [point,dite_eq_right hu0] using hm

end
end SourceLogDomain318
#print axioms SourceLogDomain318.affine_mem_of_valuation
#print axioms SourceLogDomain318.reciprocal_mem_of_valuation
