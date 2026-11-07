module
public import ActualLogMembership318
public import RestrictedBranch318
public section
namespace ActualLogIsometry318
open ClosedActualLog318 ClosedScaledEvaluation318 ActualLogHom318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _

theorem H_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    ‖HTail318.H p (D*(U p t)^4)‖=1 := by
  have hn:=RestrictedBranch318.Hscaled_near_one p hp D hD (t^4)
  have he : ‖(RestrictedEvaluation318.eval p (ScaledCoefficients318.Hscaled p hp D hD) (t^4):ℚ_[p])-1‖<1 := by
    rw [←PadicInt.coe_one,←PadicInt.coe_sub,PadicInt.norm_coe]
    exact hn
  rw [valueH_eq,PadicInt.coe_pow] at he
  have harg : D*(U p t)^4=D*(p:ℚ_[p])^4*(t:ℚ_[p])^4 := by dsimp [U]; ring
  rw [harg]
  simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right
    (show ‖HTail318.H p (D*(p:ℚ_[p])^4*(t:ℚ_[p])^4)-1‖<‖(1:ℚ_[p])‖ by
      simpa only [norm_one] using he)

theorem logarithm_chart_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    ‖logarithm p hp D (chart p hp D hD t)‖=‖U p t‖ := by
  rw [logarithm_chart,norm_mul,norm_neg,H_norm p hp D hD t,mul_one]

theorem logHom_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (P : formalSubgroup p hp D hD) :
    ‖logHom p hp D hD P‖=‖recover p hp D P.1‖ := by
  obtain ⟨t,ht⟩:=P.2
  change ‖logarithm p hp D P.1‖=_
  rw [←ht,logarithm_chart_norm,recover_chart]

theorem norm_eq_valuation_eq (a b : ℚ_[p]) (h : ‖a‖=‖b‖) :
    Padic.addValuation a=Padic.addValuation b := by
  by_cases ha : a=0
  · have hb : b=0 := norm_eq_zero.mp (by rw [←h,ha,norm_zero])
    rw [ha,hb]
  by_cases hb : b=0
  · exact (ha (norm_eq_zero.mp (by rw [h,hb,norm_zero]))).elim
  rw [Padic.addValuation.apply ha,Padic.addValuation.apply hb]
  congr 1
  rw [Padic.norm_eq_zpow_neg_valuation ha,Padic.norm_eq_zpow_neg_valuation hb] at h
  have hp1 : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact neg_injective ((zpow_right_strictMono₀ hp1).injective h)

/-- Exact filtration preservation, including the point at infinity. -/
theorem logHom_valuation (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (P : formalSubgroup p hp D hD) :
    Padic.addValuation (logHom p hp D hD P)=Padic.addValuation (recover p hp D P.1) :=
  norm_eq_valuation_eq p _ _ (logHom_norm p hp D hD P)

theorem recover_zero_iff (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (P : formalSubgroup p hp D hD) :
    recover p hp D P.1=0 ↔ P=0 := by
  constructor
  · intro h
    obtain ⟨t,ht⟩:=P.2
    rw [←ht,recover_chart] at h
    have ht0 : t=0 := U_injective p (by simpa [U] using h)
    apply Subtype.ext
    rw [←ht,ht0,chart_zero]
    rfl
  · rintro rfl
    rfl

theorem logHom_zero_iff (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (P : formalSubgroup p hp D hD) :
    logHom p hp D hD P=0 ↔ P=0 := by
  constructor
  · intro h
    apply (recover_zero_iff p hp D hD P).mp
    apply norm_eq_zero.mp
    rw [←logHom_norm,h,norm_zero]
  · rintro rfl
    exact map_zero _

theorem logHom_injective (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    Function.Injective (logHom p hp D hD) := by
  intro P Q h
  apply sub_eq_zero.mp
  apply (logHom_zero_iff p hp D hD (P-Q)).mp
  rw [map_sub,h,sub_self]

/-- Distance in logarithm coordinates is exactly the formal-parameter depth
of the actual elliptic difference. -/
theorem logHom_difference_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P Q : formalSubgroup p hp D hD) :
    ‖logHom p hp D hD P-logHom p hp D hD Q‖=‖recover p hp D (P.1-Q.1)‖ := by
  rw [←map_sub]
  exact logHom_norm p hp D hD (P-Q)

end
end ActualLogIsometry318
#print axioms ActualLogIsometry318.logHom_valuation
#print axioms ActualLogIsometry318.logHom_injective
#print axioms ActualLogIsometry318.logHom_difference_norm
