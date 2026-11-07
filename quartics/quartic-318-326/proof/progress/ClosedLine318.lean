module
public import FormalLine318
public import GeometricInverse318
public section
namespace ClosedLine318
open PowerSeries FormalLine318 RestrictedEvaluation318 ScaledClosedDisc318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
set_option maxHeartbeats 0

theorem line_restricted (z : Fin 2 → ℤ_[p]) (i : Fin 2) : Restricted p (line z i) :=
  (isRestricted_C 1 _).mul (X_restricted p)

theorem parameter_small (D : ℤ_[p]) (hD : ‖D‖<1) (z : Fin 2 → ℤ_[p]) :
    ‖D*(z 0)^2*(z 1)^2‖<1 := by
  rw [norm_mul,norm_mul]
  exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (PadicInt.norm_le_one _)).trans_lt
    ((mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_lt hD)

theorem Q_restricted (D : ℤ_[p]) (z : Fin 2 → ℤ_[p]) : Restricted p (Q D z) := by
  rw [Q_eq]
  exact GeometricInverse318.qline_restricted p _

theorem inverse_restricted (D : ℤ_[p]) (hD : ‖D‖<1) (z : Fin 2 → ℤ_[p]) :
    Restricted p ((Q D z).invOfUnit 1) := by
  rw [Q_eq]
  exact GeometricInverse318.invOfUnit_restricted p _ (parameter_small p D hD z)

theorem Vline_restricted (V : PowerSeries ℤ_[p]) (hV : Restricted p V) (z : Fin 2 → ℤ_[p]) (i : Fin 2) :
    Restricted p (V.subst (line z i)) :=
  subst_restricted p _ _ hV (line_restricted p z i) (line_zero z i)

theorem N_restricted (V : PowerSeries ℤ_[p]) (hV : Restricted p V) (z : Fin 2 → ℤ_[p]) : Restricted p (N V z) :=
  ((line_restricted p z 0).mul (Vline_restricted p V hV z 1)).add
    ((line_restricted p z 1).mul (Vline_restricted p V hV z 0))

theorem F_restricted (D : ℤ_[p]) (hD : ‖D‖<1) (V : PowerSeries ℤ_[p]) (hV : Restricted p V)
    (z : Fin 2 → ℤ_[p]) : Restricted p (F D V z) :=
  (N_restricted p V hV z).mul (inverse_restricted p D hD z)

@[simp] theorem eval_line (z : Fin 2 → ℤ_[p]) (i : Fin 2) : eval p (line z i) 1=z i := by
  rw [line,eval_mul p _ _ (isRestricted_C 1 _) (X_restricted p),eval_C,eval_X,mul_one]

/-- The full formal addition law evaluated at arbitrary integral parameters,
including units, through a one-variable pullback and proved convergence. -/
theorem evaluated_addition (D : ℤ_[p]) (hD : ‖D‖<1) (L V : PowerSeries ℤ_[p])
    (hLr : Restricted p L) (hVr : Restricted p V)
    (hL : L.map PadicInt.Coe.ringHom=GenericFormalDifferential318.integral (D:ℚ_[p]))
    (hV : V.map PadicInt.Coe.ringHom=GenericFormalDifferential318.branch (D:ℚ_[p]))
    (z : Fin 2 → ℤ_[p]) :
    eval p L (eval p (F D V z) 1)=eval p L (z 0)+eval p L (z 1) := by
  have h:=congrArg (fun f => eval p f 1) (integral_identity PadicInt.Coe.ringHom
    (fun _ _ h => PadicInt.ext h) D L V hL hV z)
  simpa only [eval_subst p L _ hLr (F_restricted p D hD V hVr z) (F_zero D V z),
    eval_add p _ _ (Vline_restricted p L hLr z 0) (Vline_restricted p L hLr z 1),
    eval_subst p L _ hLr (line_restricted p z 0) (line_zero z 0),
    eval_subst p L _ hLr (line_restricted p z 1) (line_zero z 1),eval_line] using h


theorem eval_N (V : PowerSeries ℤ_[p]) (hV : Restricted p V) (z : Fin 2 → ℤ_[p]) :
    eval p (N V z) 1=z 0*eval p V (z 1)+z 1*eval p V (z 0) := by
  rw [N,eval_add p _ _ ((line_restricted p z 0).mul (Vline_restricted p V hV z 1))
    ((line_restricted p z 1).mul (Vline_restricted p V hV z 0)),
    eval_mul p _ _ (line_restricted p z 0) (Vline_restricted p V hV z 1),
    eval_mul p _ _ (line_restricted p z 1) (Vline_restricted p V hV z 0),
    eval_subst p _ _ hV (line_restricted p z 0) (line_zero z 0),
    eval_subst p _ _ hV (line_restricted p z 1) (line_zero z 1),eval_line,eval_line]

theorem eval_inverse (D : ℤ_[p]) (hD : ‖D‖<1) (z : Fin 2 → ℤ_[p]) :
    (eval p ((Q D z).invOfUnit 1) 1:ℚ_[p])=
      (1+(D:ℚ_[p])*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)⁻¹ := by
  rw [Q_eq]
  have h:=GeometricInverse318.eval_invOfUnit_coe p _ (parameter_small p D hD z) 1
  simpa only [GeometricInverse318.qline,PadicInt.coe_one,one_pow,mul_one,PadicInt.coe_mul,PadicInt.coe_pow] using h

theorem evaluated_parameter (D : ℤ_[p]) (hD : ‖D‖<1) (V : PowerSeries ℤ_[p]) (hV : Restricted p V)
    (z : Fin 2 → ℤ_[p]) :
    (eval p (F D V z) 1:ℚ_[p])=
      ((z 0:ℚ_[p])*(eval p V (z 1):ℚ_[p])+(z 1:ℚ_[p])*(eval p V (z 0):ℚ_[p])) /
        (1+(D:ℚ_[p])*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2) := by
  rw [F,eval_mul p _ _ (N_restricted p V hV z) (inverse_restricted p D hD z),
    PadicInt.coe_mul,eval_N p V hV z,eval_inverse p D hD z]
  simp only [PadicInt.coe_add,PadicInt.coe_mul,div_eq_mul_inv]

theorem branch_square (D : ℤ_[p]) (V : PowerSeries ℤ_[p])
    (hV : V.map PadicInt.Coe.ringHom=GenericFormalDifferential318.branch (D:ℚ_[p])) :
    V^2=1-C D*X^4 := by
  apply PowerSeries.map_injective PadicInt.Coe.ringHom (fun _ _ h=>PadicInt.ext h)
  simpa only [map_pow,map_sub,map_one,map_mul,map_C,map_X,hV,PadicInt.Coe.ringHom_apply,
    GenericFormalDifferential318.argument] using GenericFormalDifferential318.branch_square (D:ℚ_[p])

theorem evaluated_curve (D : ℤ_[p]) (V : PowerSeries ℤ_[p]) (hVr : Restricted p V)
    (hV : V.map PadicInt.Coe.ringHom=GenericFormalDifferential318.branch (D:ℚ_[p])) (t : ℤ_[p]) :
    (eval p V t)^2=1-D*t^4 := by
  have h:=congrArg (fun f => eval p f t) (branch_square p D V hV)
  simpa only [eval_pow p V hVr,eval_sub p _ _ (isRestricted_one 1)
    ((isRestricted_C 1 D).mul ((X_restricted p).pow 4)),eval_one,
    eval_mul p _ _ (isRestricted_C 1 D) ((X_restricted p).pow 4),
    eval_C,eval_pow p _ (X_restricted p),eval_X] using h

theorem evaluated_ordinate (D : ℤ_[p]) (hD : ‖D‖<1) (V : PowerSeries ℤ_[p]) (hVr : Restricted p V)
    (hV : V.map PadicInt.Coe.ringHom=GenericFormalDifferential318.branch (D:ℚ_[p]))
    (z : Fin 2 → ℤ_[p]) :
    (eval p V (eval p (F D V z) 1):ℚ_[p])=
      ((eval p V (z 0):ℚ_[p])*(eval p V (z 1):ℚ_[p])*
        (1-(D:ℚ_[p])*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)-
        2*(D:ℚ_[p])*(z 0:ℚ_[p])*(z 1:ℚ_[p])*((z 0:ℚ_[p])^2+(z 1:ℚ_[p])^2)) /
        (1+(D:ℚ_[p])*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)^2 := by
  have h:=congrArg (fun f => eval p f 1) (branch_identity PadicInt.Coe.ringHom
    (fun _ _ h => PadicInt.ext h) D V hV z)
  rw [show (2:PowerSeries ℤ_[p])=C 2 from (map_ofNat C 2).symm] at h
  have hx0:=line_restricted p z 0
  have hx1:=line_restricted p z 1
  have hv0:=Vline_restricted p V hVr z 0
  have hv1:=Vline_restricted p V hVr z 1
  have hi:=inverse_restricted p D hD z
  have hc:=isRestricted_C (R:=ℤ_[p]) 1 D
  have h2:=isRestricted_C (R:=ℤ_[p]) 1 2
  have ho:=isRestricted_one (R:=ℤ_[p]) 1
  simp only [eval_subst p V _ hVr (F_restricted p D hD V hVr z) (F_zero D V z)] at h
  have hpow:= (hx0.pow 2).add (hx1.pow 2)
  have hprod:= (hc.mul (hx0.pow 2)).mul (hx1.pow 2)
  have hfirst:= (hv0.mul hv1).mul (ho.sub hprod)
  have hsecond:= (((h2.mul hc).mul hx0).mul hx1).mul hpow
  simp only [eval_mul p _ _ (hfirst.sub hsecond) (hi.pow 2),
    eval_sub p _ _ hfirst hsecond,
    eval_mul p _ _ (hv0.mul hv1) (ho.sub hprod),
    eval_mul p _ _ hv0 hv1,
    eval_sub p _ _ ho hprod,
    eval_mul p _ _ (hc.mul (hx0.pow 2)) (hx1.pow 2),
    eval_mul p _ _ hc (hx0.pow 2),
    eval_mul p _ _ (((h2.mul hc).mul hx0).mul hx1) hpow,
    eval_mul p _ _ ((h2.mul hc).mul hx0) hx1,
    eval_mul p _ _ (h2.mul hc) hx0,
    eval_mul p _ _ h2 hc,
    eval_add p _ _ (hx0.pow 2) (hx1.pow 2),
    eval_pow p _ hx0,eval_pow p _ hx1,eval_pow p _ hi,
    eval_C,eval_one] at h
  simp only [eval_subst p V _ hVr hx0 (line_zero z 0),
    eval_subst p V _ hVr hx1 (line_zero z 1),eval_line] at h
  have hh:=congrArg (fun a : ℤ_[p] => (a:ℚ_[p])) h
  have htwo : ((2:ℤ_[p]):ℚ_[p])=2 := by rfl
  simpa only [PadicInt.coe_mul,PadicInt.coe_sub,PadicInt.coe_add,PadicInt.coe_pow,
    PadicInt.coe_one,htwo,eval_inverse p D hD z,div_eq_mul_inv,inv_pow] using hh

end
end ClosedLine318
#print axioms ClosedLine318.evaluated_addition

#print axioms ClosedLine318.evaluated_ordinate
