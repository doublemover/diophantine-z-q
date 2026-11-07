module
public import EvaluatedAddition318
public import ScaledFormalSeries318
public section
namespace ScaledEvaluation318
open PadicIntEvaluation318 EvaluatedAddition318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
attribute [local instance] DiscreteTopology.instContinuousSMul

@[expose] def parameter (D : ℚ_[p]) (hD : ‖D‖≤1) : Coeff p := ScaledFormalSeries318.parameter p D hD
@[expose] def L (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) : PowerSeries (Coeff p) :=
  ScaledFormalSeries318.integralScaled p hp D hD
@[expose] def V (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) : PowerSeries (Coeff p) :=
  ScaledFormalSeries318.branchScaled p hp D hD
@[expose] def Hscaled (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) : PowerSeries (Coeff p) :=
  ScaledCoefficients318.Hscaled p hp D hD

theorem L_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    (L p hp D hD).map (toPadic p)=GenericFormalDifferential318.integral (toPadic p (parameter p D hD)) := by
  change (ScaledFormalSeries318.integralScaled p hp D hD).map PadicInt.Coe.ringHom=
    GenericFormalDifferential318.integral (ScaledFormalSeries318.parameter p D hD : ℚ_[p])
  rw [ScaledFormalSeries318.coe_parameter]
  exact ScaledFormalSeries318.map_integralScaled p hp D hD

theorem V_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    (V p hp D hD).map (toPadic p)=GenericFormalDifferential318.branch (toPadic p (parameter p D hD)) := by
  change (ScaledFormalSeries318.branchScaled p hp D hD).map PadicInt.Coe.ringHom=
    GenericFormalDifferential318.branch (ScaledFormalSeries318.parameter p D hD : ℚ_[p])
  rw [ScaledFormalSeries318.coe_parameter]
  exact ScaledFormalSeries318.map_branchScaled p hp D hD

@[expose] def valueL (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℤ_[p] :=
  PowerSeries.eval₂ (coefficientMap p) x (L p hp D hD)
@[expose] def valueV (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℤ_[p] :=
  PowerSeries.eval₂ (coefficientMap p) x (V p hp D hD)
@[expose] def sumParameter (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) : ℤ_[p] :=
  MvPowerSeries.eval₂ (coefficientMap p) z (IntegralFormalAddition318.f (parameter p D hD) (V p hp D hD))

/-- No unproved coefficient bindings or convergence assumptions remain. -/
theorem actual_scaled_addition (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    valueL p hp D hD (sumParameter p hp D hD z)=
      valueL p hp D hD (z 0)+valueL p hp D hD (z 1) :=
  evaluated_addition p _ _ _ (L_binding p hp D hD) (V_binding p hp D hD) z hz

theorem sumParameter_small (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) : ‖sumParameter p hp D hD z‖<1 :=
  evaluation_zero_small p _ (IntegralFormalAddition318.f_zero _ _) z hz

theorem valueV_spec (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (valueV p hp D hD x)^2=1-coefficientMap p (parameter p D hD)*x^4 ∧
      ‖valueV p hp D hD x-1‖<1 :=
  evaluated_branch p _ _ (V_binding p hp D hD) x hx

theorem valueH_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    ((PowerSeries.eval₂ (coefficientMap p) x (Hscaled p hp D hD) : ℤ_[p]) : ℚ_[p])=
      HTail318.H p (D*(p:ℚ_[p])^4*(x:ℚ_[p])) := by
  have hs := evaluation_hasSum p (Hscaled p hp D hD) x hx
  have hm := hs.map PadicInt.Coe.ringHom continuous_subtype_val
  have hterms : (fun n => PadicInt.Coe.ringHom
      (coefficientMap p (PowerSeries.coeff n (Hscaled p hp D hD))*x^n))=
      HTail318.term p (D*(p:ℚ_[p])^4*(x:ℚ_[p])) := by
    funext n
    have hc : coefficientMap p (PowerSeries.coeff n (Hscaled p hp D hD))=
        ScaledCoefficients318.hIntegralCoefficient p hp D hD n := by
      exact ScaledCoefficients318.coeff_Hscaled p hp D hD n
    rw [map_mul,map_pow,hc,PadicInt.Coe.ringHom_apply,ScaledCoefficients318.coe_hIntegralCoefficient]
    simp only [ScaledCoefficients318.hCoefficient,HTail318.term,mul_pow,←pow_mul,PadicInt.Coe.ringHom_apply]
    ring
  simp only [Function.comp_def] at hm
  rw [hterms] at hm
  exact hm.tsum_eq.symm


theorem valueL_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (valueL p hp D hD x:ℚ_[p])= -(x:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(x:ℚ_[p])^4) := by
  let e := PowerSeries.aeval (R:=Coeff p) (hasEval_of_norm_lt_one p x hx)
  have heval (f : PowerSeries (Coeff p)) : e f=PowerSeries.eval₂ (coefficientMap p) x f :=
    congrFun (PowerSeries.coe_aeval (hasEval_of_norm_lt_one p x hx)) f
  have heX : e PowerSeries.X=x := by rw [heval,PowerSeries.eval₂_X]
  have hL : L p hp D hD= -PowerSeries.X*(Hscaled p hp D hD).subst (PowerSeries.X^4) := rfl
  have hz : valueL p hp D hD x= -x*PowerSeries.eval₂ (coefficientMap p) (x^4) (Hscaled p hp D hD) := by
    rw [valueL,←heval,hL,map_mul,map_neg,heX,heval,
      evaluation_subst_univariate p _ _ (by simp) x hx,←heval,map_pow,heX]
  have hx4 : ‖x^4‖<1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg x) hx (by decide)
  rw [hz,PadicInt.coe_mul,PadicInt.coe_neg,valueH_eq p hp D hD (x^4) hx4,PadicInt.coe_pow]

theorem sumParameter_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    (sumParameter p hp D hD z:ℚ_[p])=
      ((z 0:ℚ_[p])*(valueV p hp D hD (z 1):ℚ_[p])+(z 1:ℚ_[p])*(valueV p hp D hD (z 0):ℚ_[p])) /
        (1+(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2) := by
  have h := evaluated_parameter p (parameter p D hD) (V p hp D hD) z hz
  change (sumParameter p hp D hD z:ℚ_[p])=_ at h
  have hd : toPadic p (parameter p D hD)=D*(p:ℚ_[p])^4 :=
    ScaledFormalSeries318.coe_parameter p D hD
  simpa only [hd,valueV] using h

/-- Actual full H-series addition in the scaled reciprocal parameter, with
all convergence and coefficient bindings discharged. Domain: norm(z_i)<1. -/
theorem actual_H_addition (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    let t := (sumParameter p hp D hD z:ℚ_[p]);
    -t*HTail318.H p (D*(p:ℚ_[p])^4*t^4)=
      -(z 0:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(z 0:ℚ_[p])^4)+
      -(z 1:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(z 1:ℚ_[p])^4) := by
  have h := congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) (actual_scaled_addition p hp D hD z hz)
  simpa only [PadicInt.coe_add,valueL_eq p hp D hD _ (sumParameter_small p hp D hD z hz),
    valueL_eq p hp D hD (z 0) (hz 0),valueL_eq p hp D hD (z 1) (hz 1)] using h


theorem valueV_eq_root (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (valueV p hp D hD x:ℚ_[p])=CanonicalRoot318.root p hp (D*(p:ℚ_[p])^4*(x:ℚ_[p])^4) := by
  have hs := valueV_spec p hp D hD x hx
  have hd : ((coefficientMap p (parameter p D hD):ℤ_[p]):ℚ_[p])=D*(p:ℚ_[p])^4 :=
    ScaledFormalSeries318.coe_parameter p D hD
  have he : ((coefficientMap p (parameter p D hD)*x^4:ℤ_[p]):ℚ_[p])=D*(p:ℚ_[p])^4*(x:ℚ_[p])^4 := by
    rw [PadicInt.coe_mul,PadicInt.coe_pow,hd]
  have hw : ‖D*(p:ℚ_[p])^4*(x:ℚ_[p])^4‖<1 := by
    rw [←he,PadicInt.norm_coe,norm_mul,norm_pow]
    exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg x) _)
      (PadicInt.norm_le_one _)).trans_lt (pow_lt_one₀ (norm_nonneg x) hx (by decide))
  have hcurve : (valueV p hp D hD x:ℚ_[p])^2=1-D*(p:ℚ_[p])^4*(x:ℚ_[p])^4 := by
    have h := congrArg (fun y : ℤ_[p] => (y:ℚ_[p])) hs.1
    simpa only [PadicInt.coe_pow,PadicInt.coe_sub,PadicInt.coe_one,he] using h
  have hnear : ‖(valueV p hp D hD x:ℚ_[p])-1‖<1 := by
    rw [←PadicInt.coe_one,←PadicInt.coe_sub,PadicInt.norm_coe]
    exact hs.2
  exact CanonicalRoot318.root_unique p hp _ _ _ hcurve (CanonicalRoot318.root_spec p hp _ hw).1
    hnear (CanonicalRoot318.root_spec p hp _ hw).2


theorem sumOrdinate_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1)
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    (valueV p hp D hD (sumParameter p hp D hD z):ℚ_[p])=
    ((valueV p hp D hD (z 0):ℚ_[p])*(valueV p hp D hD (z 1):ℚ_[p])*
      (1-(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)-
      2*(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])*(z 1:ℚ_[p])*((z 0:ℚ_[p])^2+(z 1:ℚ_[p])^2)) /
      (1+(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)^2 := by
  have h := evaluated_ordinate p (parameter p D hD) (V p hp D hD) (V_binding p hp D hD) z hz
  have hd : toPadic p (parameter p D hD)=D*(p:ℚ_[p])^4 := ScaledFormalSeries318.coe_parameter p D hD
  simpa only [hd,valueV,sumParameter] using h

theorem valueV_nonzero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (valueV p hp D hD x:ℚ_[p])≠0 := by
  intro he
  have hZ : valueV p hp D hD x=0 := PadicInt.ext he
  have h := (valueV_spec p hp D hD x hx).2
  rw [hZ,zero_sub,norm_neg,norm_one] at h
  exact lt_irrefl _ h

theorem valueV_curve (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) (hx : ‖x‖<1) :
    (valueV p hp D hD x:ℚ_[p])^2=1-(D*(p:ℚ_[p])^4)*(x:ℚ_[p])^4 := by
  have h := congrArg (fun y : ℤ_[p] => (y:ℚ_[p])) (valueV_spec p hp D hD x hx).1
  have hd : ((coefficientMap p (parameter p D hD):ℤ_[p]):ℚ_[p])=D*(p:ℚ_[p])^4 :=
    ScaledFormalSeries318.coe_parameter p D hD
  simpa only [PadicInt.coe_pow,PadicInt.coe_sub,PadicInt.coe_one,PadicInt.coe_mul,hd] using h

end
end ScaledEvaluation318
#print axioms ScaledEvaluation318.actual_scaled_addition
#print axioms ScaledEvaluation318.valueV_spec
#print axioms ScaledEvaluation318.valueH_eq

#print axioms ScaledEvaluation318.valueL_eq
#print axioms ScaledEvaluation318.sumParameter_eq
#print axioms ScaledEvaluation318.actual_H_addition

#print axioms ScaledEvaluation318.valueV_eq_root

#print axioms ScaledEvaluation318.sumOrdinate_eq
