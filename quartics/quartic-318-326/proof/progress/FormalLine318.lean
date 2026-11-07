module
public import IntegralFormalAddition318
public section
namespace FormalLine318
open PowerSeries
variable {R K : Type*} [CommRing R] [Field K] [CharZero K]
noncomputable section

@[expose] def line (z : Fin 2 → R) (i : Fin 2) : PowerSeries R := C (z i)*X
@[simp] theorem line_zero (z : Fin 2 → R) (i : Fin 2) : constantCoeff (line z i)=0 := by simp [line]
theorem line_hasSubst (z : Fin 2 → R) : MvPowerSeries.HasSubst (line z) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (line_zero z)
@[expose] def pull (z : Fin 2 → R) : IntegralFormalAddition318.S R →ₐ[R] PowerSeries R :=
  MvPowerSeries.substAlgHom (line_hasSubst z)
@[simp] theorem pull_x (z : Fin 2 → R) : pull z IntegralFormalAddition318.x=line z 0 := by
  dsimp only [pull]
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_X (R:=R) (line_hasSubst z) 0
@[simp] theorem pull_a (z : Fin 2 → R) : pull z IntegralFormalAddition318.a=line z 1 := by
  dsimp only [pull]
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_X (R:=R) (line_hasSubst z) 1
@[simp] theorem pull_C (z : Fin 2 → R) (c : R) : pull z (MvPowerSeries.C c)=C c := by
  dsimp only [pull]
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_C (a:=line z) c

theorem pull_subst (z : Fin 2 → R) (F : PowerSeries R) (g : IntegralFormalAddition318.S R)
    (hg : MvPowerSeries.constantCoeff g=0) :
    pull z (F.subst g)=F.subst (pull z g) := by
  dsimp only [pull]
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero hg).const (line_hasSubst z) F

@[expose] def Q (D : R) (z : Fin 2 → R) : PowerSeries R := 1+C D*(line z 0)^2*(line z 1)^2
@[expose] def N (V : PowerSeries R) (z : Fin 2 → R) : PowerSeries R :=
  line z 0*V.subst (line z 1)+line z 1*V.subst (line z 0)
@[expose] def F (D : R) (V : PowerSeries R) (z : Fin 2 → R) : PowerSeries R :=
  N V z*(Q D z).invOfUnit 1
@[simp] theorem Q_zero (D : R) (z : Fin 2 → R) : constantCoeff (Q D z)=1 := by simp [Q]
@[simp] theorem F_zero (D : R) (V : PowerSeries R) (z : Fin 2 → R) : constantCoeff (F D V z)=0 := by
  simp [F,N]

theorem Q_eq (D : R) (z : Fin 2 → R) : Q D z=1+C (D*(z 0)^2*(z 1)^2)*X^4 := by
  simp only [Q,line,map_mul,map_pow]
  ring

theorem pull_q (D : R) (z : Fin 2 → R) : pull z (IntegralFormalAddition318.q D)=Q D z := by
  simp only [IntegralFormalAddition318.q,map_add,map_one,map_mul,map_pow,pull_x,pull_a,pull_C,Q]

theorem pull_inverse (D : R) (z : Fin 2 → R) :
    pull z ((IntegralFormalAddition318.q D).invOfUnit 1)=(Q D z).invOfUnit 1 := by
  have h:=congrArg (pull z) (MvPowerSeries.invOfUnit_mul (IntegralFormalAddition318.q D) 1 (by simp))
  simp only [map_mul,map_one,pull_q] at h
  calc
    _ = pull z ((IntegralFormalAddition318.q D).invOfUnit 1) *
        (Q D z*(Q D z).invOfUnit 1) := by rw [MvPowerSeries.mul_invOfUnit _ 1 (by change PowerSeries.constantCoeff (Q D z)=1; simp),mul_one]
    _ = (Q D z).invOfUnit 1 := by rw [←mul_assoc,h,one_mul]

theorem pull_f (D : R) (V : PowerSeries R) (z : Fin 2 → R) :
    pull z (IntegralFormalAddition318.f D V)=F D V z := by
  simp only [IntegralFormalAddition318.f,IntegralFormalAddition318.n,IntegralFormalAddition318.v,
    map_mul,map_add,pull_x,pull_a,pull_inverse,
    pull_subst z V _ IntegralFormalAddition318.x_zero,
    pull_subst z V _ IntegralFormalAddition318.a_zero,F,N]

theorem integral_identity (φ : R →+* K) (hφ : Function.Injective φ) (D : R) (L V : PowerSeries R)
    (hL : L.map φ=GenericFormalDifferential318.integral (φ D))
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) (z : Fin 2 → R) :
    L.subst (F D V z)=L.subst (line z 0)+L.subst (line z 1) := by
  have h:=congrArg (pull z) (IntegralFormalAddition318.formal_addition φ hφ D L V hL hV)
  simpa only [map_add,pull_subst z L _ (IntegralFormalAddition318.f_zero D V),
    pull_subst z L _ IntegralFormalAddition318.x_zero,pull_subst z L _ IntegralFormalAddition318.a_zero,
    pull_f,pull_x,pull_a] using h

theorem branch_identity (φ : R →+* K) (hφ : Function.Injective φ) (D : R) (V : PowerSeries R)
    (hV : V.map φ=GenericFormalDifferential318.branch (φ D)) (z : Fin 2 → R) :
    V.subst (F D V z)=
      (V.subst (line z 0)*V.subst (line z 1)*(1-C D*(line z 0)^2*(line z 1)^2)-
        2*C D*line z 0*line z 1*((line z 0)^2+(line z 1)^2))*((Q D z).invOfUnit 1)^2 := by
  have h:=congrArg (pull z) (IntegralFormalAddition318.formal_branch φ hφ D V hV)
  simpa only [map_mul,map_sub,map_add,map_one,map_ofNat,map_pow,pull_C,
    pull_subst z V _ (IntegralFormalAddition318.f_zero D V),IntegralFormalAddition318.v,
    pull_subst z V _ IntegralFormalAddition318.x_zero,pull_subst z V _ IntegralFormalAddition318.a_zero,
    pull_f,pull_x,pull_a,pull_inverse] using h

end
end FormalLine318
#print axioms FormalLine318.integral_identity
#print axioms FormalLine318.branch_identity
