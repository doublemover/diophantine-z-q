module
public import ClosedLine318
public import RestrictedBranch318
public import CanonicalRoot318
public section
namespace ClosedScaledEvaluation318
open PowerSeries RestrictedEvaluation318 ScaledCoefficients318 ScaledFormalSeries318 ScaledClosedDisc318
variable (p : ℕ) [Fact p.Prime]
noncomputable section

@[expose] def valueL (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℤ_[p] :=
  eval p (integralScaled p hp D hD) x
@[expose] def valueV (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) : ℤ_[p] :=
  eval p (branchScaled p hp D hD) x
@[expose] def sumParameter (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) : ℤ_[p] :=
  eval p (FormalLine318.F (parameter p D hD) (branchScaled p hp D hD) z) 1

theorem parameter_small (D : ℚ_[p]) (hD : ‖D‖≤1) : ‖parameter p D hD‖<1 := by
  rw [parameter,norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (PadicInt.norm_le_one _)).trans_lt
  exact pow_lt_one₀ (norm_nonneg _) (by simpa only [←PadicInt.norm_coe,PadicInt.coe_natCast] using (Padic.norm_p_lt_one (p:=p))) (by decide)

theorem L_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    (integralScaled p hp D hD).map PadicInt.Coe.ringHom=
      GenericFormalDifferential318.integral (parameter p D hD:ℚ_[p]) := by
  rw [coe_parameter]
  exact map_integralScaled p hp D hD

theorem V_binding (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) :
    (branchScaled p hp D hD).map PadicInt.Coe.ringHom=
      GenericFormalDifferential318.branch (parameter p D hD:ℚ_[p]) := by
  rw [coe_parameter]
  exact map_branchScaled p hp D hD

theorem actual_addition (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) :
    valueL p hp D hD (sumParameter p hp D hD z)=valueL p hp D hD (z 0)+valueL p hp D hD (z 1) :=
  ClosedLine318.evaluated_addition p _ (parameter_small p D hD) _ _
    (integralScaled_restricted p hp D hD) (branchScaled_restricted p hp D hD)
    (L_binding p hp D hD) (V_binding p hp D hD) z

theorem valueH_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (eval p (Hscaled p hp D hD) x:ℚ_[p])=HTail318.H p (D*(p:ℚ_[p])^4*(x:ℚ_[p])) := by
  have hs := eval_hasSum p (Hscaled p hp D hD) (Hscaled_restricted p hp D hD) x
  have hm := hs.map PadicInt.Coe.ringHom continuous_subtype_val
  have hterms : (fun n => PadicInt.Coe.ringHom (coeff n (Hscaled p hp D hD)*x^n))=
      HTail318.term p (D*(p:ℚ_[p])^4*(x:ℚ_[p])) := by
    funext n
    rw [map_mul,map_pow,coeff_Hscaled,PadicInt.Coe.ringHom_apply,coe_hIntegralCoefficient]
    simp only [hCoefficient,HTail318.term,mul_pow,←pow_mul,PadicInt.Coe.ringHom_apply]
    ring
  simp only [Function.comp_def] at hm
  rw [hterms] at hm
  exact hm.tsum_eq.symm

theorem valueL_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (valueL p hp D hD x:ℚ_[p])= -(x:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(x:ℚ_[p])^4) := by
  rw [valueL,eval_integralScaled,PadicInt.coe_mul,PadicInt.coe_neg,valueH_eq,PadicInt.coe_pow]

theorem actual_H_addition (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) :
    let t := (sumParameter p hp D hD z:ℚ_[p]);
    -t*HTail318.H p (D*(p:ℚ_[p])^4*t^4)=
      -(z 0:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(z 0:ℚ_[p])^4)+
      -(z 1:ℚ_[p])*HTail318.H p (D*(p:ℚ_[p])^4*(z 1:ℚ_[p])^4) := by
  have h:=congrArg (fun a : ℤ_[p] => (a:ℚ_[p])) (actual_addition p hp D hD z)
  simpa only [PadicInt.coe_add,valueL_eq] using h

theorem sumParameter_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) :
    (sumParameter p hp D hD z:ℚ_[p])=
      ((z 0:ℚ_[p])*(valueV p hp D hD (z 1):ℚ_[p])+(z 1:ℚ_[p])*(valueV p hp D hD (z 0):ℚ_[p])) /
        (1+(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2) := by
  have h:=ClosedLine318.evaluated_parameter p _ (parameter_small p D hD) _
    (branchScaled_restricted p hp D hD) z
  simpa only [coe_parameter,valueV,sumParameter] using h

theorem valueV_curve (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (valueV p hp D hD x:ℚ_[p])^2=1-(D*(p:ℚ_[p])^4)*(x:ℚ_[p])^4 := by
  have h:=congrArg (fun a : ℤ_[p] => (a:ℚ_[p])) (ClosedLine318.evaluated_curve p _ _
    (branchScaled_restricted p hp D hD) (V_binding p hp D hD) x)
  simpa only [valueV,PadicInt.coe_pow,PadicInt.coe_sub,PadicInt.coe_one,PadicInt.coe_mul,coe_parameter] using h

theorem sumOrdinate_eq (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (z : Fin 2 → ℤ_[p]) :
    (valueV p hp D hD (sumParameter p hp D hD z):ℚ_[p])=
      ((valueV p hp D hD (z 0):ℚ_[p])*(valueV p hp D hD (z 1):ℚ_[p])*
        (1-(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)-
        2*(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])*(z 1:ℚ_[p])*((z 0:ℚ_[p])^2+(z 1:ℚ_[p])^2)) /
        (1+(D*(p:ℚ_[p])^4)*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)^2 := by
  have h:=ClosedLine318.evaluated_ordinate p _ (parameter_small p D hD) _
    (branchScaled_restricted p hp D hD) (V_binding p hp D hD) z
  simpa only [coe_parameter,valueV,sumParameter] using h


theorem valueV_near_one (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    ‖valueV p hp D hD x-1‖<1 :=
  RestrictedBranch318.branchScaled_near_one p hp D hD x

theorem valueV_nonzero (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (valueV p hp D hD x:ℚ_[p])≠0 := by
  intro he
  have hZ : valueV p hp D hD x=0 := PadicInt.ext he
  have h:=valueV_near_one p hp D hD x
  rw [hZ,zero_sub,norm_neg,norm_one] at h
  exact lt_irrefl _ h

theorem valueV_eq_root (hp : 19≤p) (D : ℚ_[p]) (hD : ‖D‖≤1) (x : ℤ_[p]) :
    (valueV p hp D hD x:ℚ_[p])=CanonicalRoot318.root p hp (D*(p:ℚ_[p])^4*(x:ℚ_[p])^4) := by
  have he : ((parameter p D hD*x^4:ℤ_[p]):ℚ_[p])=D*(p:ℚ_[p])^4*(x:ℚ_[p])^4 := by
    rw [PadicInt.coe_mul,PadicInt.coe_pow,coe_parameter]
  have hw : ‖D*(p:ℚ_[p])^4*(x:ℚ_[p])^4‖<1 := by
    rw [←he,PadicInt.norm_coe,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt (parameter_small p D hD)
  have hnear : ‖(valueV p hp D hD x:ℚ_[p])-1‖<1 := by
    rw [←PadicInt.coe_one,←PadicInt.coe_sub,PadicInt.norm_coe]
    exact valueV_near_one p hp D hD x
  exact CanonicalRoot318.root_unique p hp _ _ _ (valueV_curve p hp D hD x)
    (CanonicalRoot318.root_spec p hp _ hw).1 hnear (CanonicalRoot318.root_spec p hp _ hw).2

end
end ClosedScaledEvaluation318
#print axioms ClosedScaledEvaluation318.actual_H_addition
#print axioms ClosedScaledEvaluation318.sumOrdinate_eq

#print axioms ClosedScaledEvaluation318.valueV_eq_root
