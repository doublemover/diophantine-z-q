module
public import ActualLogRatio318
public section
namespace FormalLogDepth318
open ClosedActualLog318 ClosedScaledEvaluation318 ActualLogHom318 ActualLogIsometry318
open ActualLogIdentification318 ActualLogRatio318
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem w_depth (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1) (hDu:Padic.addValuation D=0)
    (P:formalSubgroup p hp D hD) (r:ℤ)
    (hr:Padic.addValuation (logHom p hp D hD P)=(r:ℤ)) :
    (wParameter p D P.1).valuation=4*r := by
  obtain ⟨t,ht⟩:=P.2
  have hu:Padic.addValuation (U p t)=(r:ℤ) := by
    rw [logHom_valuation] at hr
    simpa only [←ht,recover_chart] using hr
  have hw:Padic.addValuation (wParameter p D P.1)=((4*r:ℤ):WithTop ℤ) := by
    rw [←ht,wParameter_chart,Padic.addValuation.map_mul,Padic.addValuation.map_pow,hDu,hu,zero_add]
    norm_cast
  have hn:wParameter p D P.1≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hw]; exact WithTop.coe_ne_top)
  rw [Padic.addValuation.apply hn] at hw
  exact WithTop.coe_inj.mp hw

theorem ratio_valuation (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1)
    (P Q:formalSubgroup p hp D hD) :
    Padic.addValuation (logHom p hp D hD P/logHom p hp D hD Q)=
      Padic.addValuation (zParameter p D P.1/zParameter p D Q.1) := by
  rw [Padic.addValuation.map_div,Padic.addValuation.map_div,logHom_z_valuation,logHom_z_valuation]

/-- Once an actual logarithm ratio is integral, the first-order parameter
approximation has absolute precision four times the denominator depth.
This includes the numerator identity point and requires no chosen chart. -/
theorem integral_first_order (hp:19≤p) (D:ℚ_[p]) (hD:‖D‖≤1)
    (hDu:Padic.addValuation D=0) (P Q:formalSubgroup p hp D hD) (s:ℤ) (hs:1≤s)
    (hQ:Padic.addValuation (logHom p hp D hD Q)=(s:ℤ))
    (hi:0≤Padic.addValuation (logHom p hp D hD P/logHom p hp D hD Q)) :
    ((4*s:ℤ):WithTop ℤ)≤Padic.addValuation
      (logHom p hp D hD P/logHom p hp D hD Q-zParameter p D P.1/zParameter p D Q.1) := by
  by_cases hP:logHom p hp D hD P=0
  · have hz:zParameter p D P.1=0 := by
      apply norm_eq_zero.mp
      rw [←logHom_z_norm,hP,norm_zero]
    simp [hP,hz]
  obtain ⟨r,hr⟩:=WithTop.ne_top_iff_exists.mp ((Padic.addValuation.ne_top_iff).mpr hP)
  have hrs:s≤r := by
    rw [Padic.addValuation.map_div,←hr,hQ,←WithTop.LinearOrderedAddCommGroup.coe_sub] at hi
    have hh:0≤r-s := WithTop.coe_le_coe.mp hi
    omega
  have hParg:=w_depth p hp D hD hDu P r hr.symm
  have hQarg:=w_depth p hp D hD hDu Q s hQ
  have he:=first_order_ratio_precision p hp D hD P Q r s (by omega) hs (Or.inr hParg) (Or.inr hQarg)
  rw [min_eq_right hrs] at he
  have hv:0≤Padic.addValuation (zParameter p D P.1/zParameter p D Q.1) := by
    rwa [←ratio_valuation]
  exact (show ((4*s:ℤ):WithTop ℤ)≤Padic.addValuation (zParameter p D P.1/zParameter p D Q.1)+((4*s:ℤ):WithTop ℤ) by
    simpa using add_le_add hv (le_refl ((4*s:ℤ):WithTop ℤ))).trans he

end
end FormalLogDepth318
#print axioms FormalLogDepth318.integral_first_order
