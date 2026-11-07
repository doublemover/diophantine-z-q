module
public import FormalLine318
public import IntegralGeometricInverse318
public section
namespace IntegralLine318
open PowerSeries FormalLine318 IntegralRingEvaluation318 IntegralGeometricInverse318
variable (R : Type*) [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R]
  [NormBoundOne R]
variable {K : Type*} [Field K] [CharZero K] (φ : R →+* K) (hφ : Function.Injective φ)
noncomputable section
set_option maxHeartbeats 0

theorem line_restricted (z : Fin 2 → R) (i : Fin 2) : Restricted R (line z i) :=
  (isRestricted_C 1 _).mul (X_restricted R)

theorem parameter_small (D : R) (hD : ‖D‖<1) (z : Fin 2 → R) :
    ‖D*(z 0)^2*(z 1)^2‖<1 := by
  exact (norm_mul_le _ _).trans_lt
    ((mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _)).trans_lt
      ((norm_mul_le _ _).trans_lt
        ((mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _)).trans_lt hD)))

theorem Q_restricted (D : R) (z : Fin 2 → R) : Restricted R (Q D z) := by
  rw [Q_eq]
  exact IntegralGeometricInverse318.qline_restricted R _

theorem inverse_restricted (D : R) (hD : ‖D‖<1) (z : Fin 2 → R) :
    Restricted R ((Q D z).invOfUnit 1) := by
  rw [Q_eq]
  exact IntegralGeometricInverse318.invOfUnit_restricted R _ (parameter_small R D hD z)

theorem Vline_restricted (V : PowerSeries R) (hV : Restricted R V) (z : Fin 2 → R) (i : Fin 2) :
    Restricted R (V.subst (line z i)) :=
  subst_restricted R _ _ hV (line_restricted R z i) (line_zero z i)

theorem N_restricted (V : PowerSeries R) (hV : Restricted R V) (z : Fin 2 → R) : Restricted R (N V z) :=
  ((line_restricted R z 0).mul (Vline_restricted R V hV z 1)).add
    ((line_restricted R z 1).mul (Vline_restricted R V hV z 0))

theorem F_restricted (D : R) (hD : ‖D‖<1) (V : PowerSeries R) (hV : Restricted R V)
    (z : Fin 2 → R) : Restricted R (F D V z) :=
  (N_restricted R V hV z).mul (inverse_restricted R D hD z)

@[simp] theorem eval_line (z : Fin 2 → R) (i : Fin 2) : eval R (line z i) 1=z i := by
  rw [line,eval_mul R _ _ (isRestricted_C 1 _) (X_restricted R),eval_C,eval_X,mul_one]

/- The full formal addition law evaluated at arbitrary integral parameters,
including units, through a one-variable pullback and proved convergence. -/
include hφ in
theorem evaluated_addition (D : R) (hD : ‖D‖<1) (L V : PowerSeries R)
    (hLr : Restricted R L) (hVr : Restricted R V)
    (hL : L.map φ=GenericFormalDifferential318.integral (φ D))
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D))
    (z : Fin 2 → R) :
    eval R L (eval R (F D V z) 1)=eval R L (z 0)+eval R L (z 1) := by
  have h:=congrArg (fun f => eval R f 1) (integral_identity φ
    hφ D L V hL hV z)
  simpa only [eval_subst R L _ hLr (F_restricted R D hD V hVr z) (F_zero D V z),
    eval_add R _ _ (Vline_restricted R L hLr z 0) (Vline_restricted R L hLr z 1),
    eval_subst R L _ hLr (line_restricted R z 0) (line_zero z 0),
    eval_subst R L _ hLr (line_restricted R z 1) (line_zero z 1),eval_line] using h


theorem eval_N (V : PowerSeries R) (hV : Restricted R V) (z : Fin 2 → R) :
    eval R (N V z) 1=z 0*eval R V (z 1)+z 1*eval R V (z 0) := by
  rw [N,eval_add R _ _ ((line_restricted R z 0).mul (Vline_restricted R V hV z 1))
    ((line_restricted R z 1).mul (Vline_restricted R V hV z 0)),
    eval_mul R _ _ (line_restricted R z 0) (Vline_restricted R V hV z 1),
    eval_mul R _ _ (line_restricted R z 1) (Vline_restricted R V hV z 0),
    eval_subst R _ _ hV (line_restricted R z 0) (line_zero z 0),
    eval_subst R _ _ hV (line_restricted R z 1) (line_zero z 1),eval_line,eval_line]

theorem eval_inverse (D : R) (hD : ‖D‖<1) (z : Fin 2 → R) :
    φ (eval R ((Q D z).invOfUnit 1) 1)=
      (1+φ (D)*φ (z 0)^2*φ (z 1)^2)⁻¹ := by
  rw [Q_eq]
  have h:=IntegralGeometricInverse318.eval_invOfUnit_map R φ _ (parameter_small R D hD z) 1
  simpa only [IntegralGeometricInverse318.qline,map_one,one_pow,mul_one,map_mul,map_pow] using h

theorem evaluated_parameter (D : R) (hD : ‖D‖<1) (V : PowerSeries R) (hV : Restricted R V)
    (z : Fin 2 → R) :
    φ (eval R (F D V z) 1)=
      (φ (z 0)*φ (eval R V (z 1))+φ (z 1)*φ (eval R V (z 0))) /
        (1+φ (D)*φ (z 0)^2*φ (z 1)^2) := by
  rw [F,eval_mul R _ _ (N_restricted R V hV z) (inverse_restricted R D hD z),
    map_mul,eval_N R V hV z,eval_inverse R φ D hD z]
  simp only [map_add,map_mul,div_eq_mul_inv]

include hφ in
theorem branch_square (D : R) (V : PowerSeries R)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) :
    V^2=1-C D*X^4 := by
  apply PowerSeries.map_injective φ hφ
  simpa only [map_pow,map_sub,map_one,map_mul,map_C,map_X,hV,
    GenericFormalDifferential318.argument] using GenericFormalDifferential318.branch_square (φ D)

include hφ in
theorem evaluated_curve (D : R) (V : PowerSeries R) (hVr : Restricted R V)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) (t : R) :
    (eval R V t)^2=1-D*t^4 := by
  have h:=congrArg (fun f => eval R f t) (branch_square R φ hφ D V hV)
  simpa only [eval_pow R V hVr,eval_sub R _ _ (isRestricted_one 1)
    ((isRestricted_C 1 D).mul ((X_restricted R).pow 4)),eval_one,
    eval_mul R _ _ (isRestricted_C 1 D) ((X_restricted R).pow 4),
    eval_C,eval_pow R _ (X_restricted R),eval_X] using h

include hφ in
theorem evaluated_ordinate (D : R) (hD : ‖D‖<1) (V : PowerSeries R) (hVr : Restricted R V)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D))
    (z : Fin 2 → R) :
    φ (eval R V (eval R (F D V z) 1))=
      (φ (eval R V (z 0))*φ (eval R V (z 1))*
        (1-φ (D)*φ (z 0)^2*φ (z 1)^2)-
        2*φ (D)*φ (z 0)*φ (z 1)*(φ (z 0)^2+φ (z 1)^2)) /
        (1+φ (D)*φ (z 0)^2*φ (z 1)^2)^2 := by
  have h:=congrArg (fun f => eval R f 1) (branch_identity φ
    hφ D V hV z)
  rw [show (2:PowerSeries R)=C 2 from (map_ofNat C 2).symm] at h
  have hx0:=line_restricted R z 0
  have hx1:=line_restricted R z 1
  have hv0:=Vline_restricted R V hVr z 0
  have hv1:=Vline_restricted R V hVr z 1
  have hi:=inverse_restricted R D hD z
  have hc:=isRestricted_C (R:=R) 1 D
  have h2:=isRestricted_C (R:=R) 1 2
  have ho:=isRestricted_one (R:=R) 1
  simp only [eval_subst R V _ hVr (F_restricted R D hD V hVr z) (F_zero D V z)] at h
  have hpow:= (hx0.pow 2).add (hx1.pow 2)
  have hprod:= (hc.mul (hx0.pow 2)).mul (hx1.pow 2)
  have hfirst:= (hv0.mul hv1).mul (ho.sub hprod)
  have hsecond:= (((h2.mul hc).mul hx0).mul hx1).mul hpow
  simp only [eval_mul R _ _ (hfirst.sub hsecond) (hi.pow 2),
    eval_sub R _ _ hfirst hsecond,
    eval_mul R _ _ (hv0.mul hv1) (ho.sub hprod),
    eval_mul R _ _ hv0 hv1,
    eval_sub R _ _ ho hprod,
    eval_mul R _ _ (hc.mul (hx0.pow 2)) (hx1.pow 2),
    eval_mul R _ _ hc (hx0.pow 2),
    eval_mul R _ _ (((h2.mul hc).mul hx0).mul hx1) hpow,
    eval_mul R _ _ ((h2.mul hc).mul hx0) hx1,
    eval_mul R _ _ (h2.mul hc) hx0,
    eval_mul R _ _ h2 hc,
    eval_add R _ _ (hx0.pow 2) (hx1.pow 2),
    eval_pow R _ hx0,eval_pow R _ hx1,eval_pow R _ hi,
    eval_C,eval_one] at h
  simp only [eval_subst R V _ hVr hx0 (line_zero z 0),
    eval_subst R V _ hVr hx1 (line_zero z 1),eval_line] at h
  have hh:=congrArg (fun a : R => φ (a)) h
  have htwo : φ ((2:R))=2 := map_ofNat φ 2
  simpa only [map_mul,map_sub,map_add,map_pow,
    map_one,htwo,eval_inverse R φ D hD z,div_eq_mul_inv,inv_pow] using hh

end
end IntegralLine318
#print axioms IntegralLine318.evaluated_addition

#print axioms IntegralLine318.evaluated_ordinate
