module
public import ActualLogIsometry318
public section
namespace ActualLogIdentification318
open ClosedActualLog318 ClosedScaledEvaluation318 ActualLogHom318 ActualLogIsometry318
  ReciprocalDouble318 WeierstrassCurve.Affine
variable (p : ℕ) [Fact p.Prime]
noncomputable section
local instance : DecidableEq ℚ_[p] := Classical.decEq _
set_option maxHeartbeats 0

@[expose] def zParameter (D : ℚ_[p]) : (E D).Point → ℚ_[p]
  | .zero => 0
  | .some x y _ => -x/y
@[expose] def wParameter (D : ℚ_[p]) : (E D).Point → ℚ_[p]
  | .zero => 0
  | .some x _ _ => D/x^2

theorem zParameter_chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    zParameter p D (chart p hp D hD t)= -U p t/V p hp D hD t := by
  by_cases hu : U p t=0
  · simp [chart,point,hu,zParameter]
  · simp only [chart,point,dite_eq_right hu,zParameter]
    have hv : V p hp D hD t≠0 := valueV_nonzero p hp D hD t
    field_simp [hu,hv]

theorem wParameter_chart (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    wParameter p D (chart p hp D hD t)=D*(U p t)^4 := by
  by_cases hu : U p t=0
  · simp [chart,point,hu,wParameter]
  · simp only [chart,point,dite_eq_right hu,wParameter]
    field_simp

theorem V_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (t : ℤ_[p]) :
    ‖V p hp D hD t‖=1 := by
  have hn:=valueV_near_one p hp D hD t
  have hn' : ‖V p hp D hD t-1‖<‖(1:ℚ_[p])‖ := by
    simpa only [V,←PadicInt.coe_one,←PadicInt.coe_sub,PadicInt.norm_coe,norm_one] using hn
  simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right hn'

/-- The actual additive logarithm is precisely the canonical z·G(w) factor,
independent of the sign of an externally supplied reciprocal chart. -/
theorem logHom_eq_primitive (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P : formalSubgroup p hp D hD) :
    logHom p hp D hD P=CanonicalRoot318.primitive p hp (zParameter p D P.1) (wParameter p D P.1) := by
  obtain ⟨t,ht⟩:=P.2
  change logarithm p hp D P.1=_
  rw [←ht,logarithm_chart,zParameter_chart,wParameter_chart,
    CanonicalRoot318.primitive,CanonicalRoot318.factor,GTail318.G,←root_binding p hp D hD t]
  have hv : V p hp D hD t≠0 := valueV_nonzero p hp D hD t
  field_simp [hv]

theorem logHom_z_norm (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P : formalSubgroup p hp D hD) :
    ‖logHom p hp D hD P‖=‖zParameter p D P.1‖ := by
  obtain ⟨t,ht⟩:=P.2
  change ‖logarithm p hp D P.1‖=_
  rw [←ht,logarithm_chart_norm,zParameter_chart,norm_div,norm_neg,V_norm,div_one]

theorem logHom_z_valuation (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P : formalSubgroup p hp D hD) :
    Padic.addValuation (logHom p hp D hD P)=Padic.addValuation (zParameter p D P.1) :=
  norm_eq_valuation_eq p _ _ (logHom_z_norm p hp D hD P)

/-- The previously proved Padé bound now applies to the actual group logarithm,
not merely to a standalone analytic candidate. -/
theorem logHom_pade_error (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P : formalSubgroup p hp D hD) (r : ℤ) (hr : 1≤r)
    (hw : wParameter p D P.1=0 ∨ (wParameter p D P.1).valuation=4*r) :
    Padic.addValuation (zParameter p D P.1)+((16*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (logHom p hp D hD P-zParameter p D P.1*
        (Pade21Domains.PG (wParameter p D P.1)/Pade21Domains.QG (wParameter p D P.1))) := by
  rw [logHom_eq_primitive]
  exact CanonicalRoot318.primitive_pade_error p hp _ _ r hr hw

theorem logHom_first_order_error (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (P : formalSubgroup p hp D hD) (r : ℤ) (hr : 1≤r)
    (hw : wParameter p D P.1=0 ∨ (wParameter p D P.1).valuation=4*r) :
    Padic.addValuation (zParameter p D P.1)+((4*r:ℤ):WithTop ℤ)≤Padic.addValuation
      (logHom p hp D hD P-zParameter p D P.1) := by
  rw [logHom_eq_primitive]
  exact CanonicalRoot318.primitive_error p hp _ _ r hr hw

end
end ActualLogIdentification318
#print axioms ActualLogIdentification318.logHom_eq_primitive
#print axioms ActualLogIdentification318.logHom_z_valuation
#print axioms ActualLogIdentification318.logHom_pade_error
