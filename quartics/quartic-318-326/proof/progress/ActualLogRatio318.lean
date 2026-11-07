module
public import ActualLogIdentification318
public section
namespace ActualLogRatio318
open ActualLogHom318 ActualLogIdentification318 CanonicalRoot318 Pade21Domains
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- Division by units preserves a simultaneous error bound. -/
theorem ratio_error {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (A B C D : K) (k : WithTop ℤ) (hB : v B=0) (hC : v C=0) (hD : v D=0)
    (hA : k≤v (A-C)) (hBD : k≤v (B-D)) : k≤v (A/B-C/D) := by
  have hB0 : B≠0 := (v.ne_top_iff).mp (by rw [hB]; simp)
  have hD0 : D≠0 := (v.ne_top_iff).mp (by rw [hD]; simp)
  have he : A/B-C/D=((A-C)*D-C*(B-D))/(B*D) := by field_simp; ring
  rw [he,v.map_div,v.map_mul,hB,hD,zero_add,sub_zero]
  apply v.map_le_sub
  · simpa only [v.map_mul,hD,add_zero] using hA
  · simpa only [v.map_mul,hC,zero_add] using hBD

theorem approximate_unit {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (A B : K) (hA : v A=0) (h : 0<v (A-B)) : v B=0 := by
  have hh := v.map_sub_eq_of_lt_left (show v A<v (A-B) by rw [hA]; exact h)
  simpa only [sub_sub_cancel,hA] using hh

theorem pade_factor_unit (hp : 19≤p) (w : ℚ_[p]) (r : ℤ) (hr : 1≤r)
    (hw : w=0 ∨ w.valuation=4*r) : Padic.addValuation (PG w/QG w)=0 := by
  apply approximate_unit Padic.addValuation (factor p hp w) _ (factor_unit p hp w r hr hw)
  have hpos : (0:WithTop ℤ)<((16*r:ℤ):WithTop ℤ) := by exact_mod_cast (show (0:ℤ)<16*r by omega)
  exact hpos.trans_le (factor_pade_precision p hp w r hr hw)

theorem log_ratio (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) :
    logHom p hp D hD P/logHom p hp D hD Q=
      (zParameter p D P.1/zParameter p D Q.1)*
        (factor p hp (wParameter p D P.1)/factor p hp (wParameter p D Q.1)) := by
  rw [logHom_eq_primitive,logHom_eq_primitive,primitive,primitive]
  rw [div_mul_div_comm]

theorem first_order_ratio_precision (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) (r s : ℤ) (hr : 1≤r) (hs : 1≤s)
    (hwP : wParameter p D P.1=0 ∨ (wParameter p D P.1).valuation=4*r)
    (hwQ : wParameter p D Q.1=0 ∨ (wParameter p D Q.1).valuation=4*s) :
    Padic.addValuation (zParameter p D P.1/zParameter p D Q.1)+((4*min r s:ℤ):WithTop ℤ)≤
      Padic.addValuation (logHom p hp D hD P/logHom p hp D hD Q-zParameter p D P.1/zParameter p D Q.1) := by
  have hpr : ((4*min r s:ℤ):WithTop ℤ)≤((4*r:ℤ):WithTop ℤ) := by
    exact_mod_cast (show 4*min r s≤4*r by omega)
  have hps : ((4*min r s:ℤ):WithTop ℤ)≤((4*s:ℤ):WithTop ℤ) := by
    exact_mod_cast (show 4*min r s≤4*s by omega)
  have he:=ratio_error Padic.addValuation (factor p hp (wParameter p D P.1))
    (factor p hp (wParameter p D Q.1)) 1 1 ((4*min r s:ℤ):WithTop ℤ)
    (factor_unit p hp _ s hs hwQ) Padic.addValuation.map_one Padic.addValuation.map_one
    (hpr.trans (factor_relative_precision p hp _ r hr hwP))
    (hps.trans (factor_relative_precision p hp _ s hs hwQ))
  rw [div_self one_ne_zero] at he
  rw [log_ratio]
  rw [show (zParameter p D P.1/zParameter p D Q.1)*
      (factor p hp (wParameter p D P.1)/factor p hp (wParameter p D Q.1))-
      zParameter p D P.1/zParameter p D Q.1=
      (zParameter p D P.1/zParameter p D Q.1)*
      (factor p hp (wParameter p D P.1)/factor p hp (wParameter p D Q.1)-1) by ring,
    Padic.addValuation.map_mul]
  exact add_le_add le_rfl he

theorem pade_ratio_precision (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) (r s : ℤ) (hr : 1≤r) (hs : 1≤s)
    (hwP : wParameter p D P.1=0 ∨ (wParameter p D P.1).valuation=4*r)
    (hwQ : wParameter p D Q.1=0 ∨ (wParameter p D Q.1).valuation=4*s) :
    Padic.addValuation (zParameter p D P.1/zParameter p D Q.1)+((16*min r s:ℤ):WithTop ℤ)≤
      Padic.addValuation (logHom p hp D hD P/logHom p hp D hD Q-
        (zParameter p D P.1/zParameter p D Q.1)*
        ((PG (wParameter p D P.1)/QG (wParameter p D P.1))/
          (PG (wParameter p D Q.1)/QG (wParameter p D Q.1)))) := by
  have hpr : ((16*min r s:ℤ):WithTop ℤ)≤((16*r:ℤ):WithTop ℤ) := by
    exact_mod_cast (show 16*min r s≤16*r by omega)
  have hps : ((16*min r s:ℤ):WithTop ℤ)≤((16*s:ℤ):WithTop ℤ) := by
    exact_mod_cast (show 16*min r s≤16*s by omega)
  have he:=ratio_error Padic.addValuation (factor p hp (wParameter p D P.1))
    (factor p hp (wParameter p D Q.1))
    (PG (wParameter p D P.1)/QG (wParameter p D P.1))
    (PG (wParameter p D Q.1)/QG (wParameter p D Q.1)) ((16*min r s:ℤ):WithTop ℤ)
    (factor_unit p hp _ s hs hwQ) (pade_factor_unit p hp _ r hr hwP) (pade_factor_unit p hp _ s hs hwQ)
    (hpr.trans (factor_pade_precision p hp _ r hr hwP))
    (hps.trans (factor_pade_precision p hp _ s hs hwQ))
  rw [log_ratio,←mul_sub,Padic.addValuation.map_mul]
  exact add_le_add le_rfl he

end
end ActualLogRatio318
#print axioms ActualLogRatio318.first_order_ratio_precision
#print axioms ActualLogRatio318.pade_ratio_precision
