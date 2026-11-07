module
public import FormalDifferential318
public section
namespace GenericFormalDifferential318
open PowerSeries
open scoped PowerSeries
variable {K : Type*} [Field K] [CharZero K]

@[expose] noncomputable def H : PowerSeries K := FormalDifferential318.H.map (Rat.castHom K)
@[expose] noncomputable def B : PowerSeries K := FormalDifferential318.B.map (Rat.castHom K)

theorem derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) : derivative (f.map φ)=(derivative f).map φ := by
  ext n
  simp only [coeff_derivative,coeff_map,map_mul,map_add,map_natCast,map_one]

theorem H_ode : 4*(derivative (H (K:=K))*X)+H=B := by
  have h := congrArg (PowerSeries.map (Rat.castHom K)) FormalDifferential318.H_ode
  simpa only [map_add,map_mul,map_ofNat,map_X,←derivative_map,H,B] using h

theorem B_square : (1-X)*(B (K:=K))^2=1 := by
  have h := congrArg (PowerSeries.map (Rat.castHom K)) FormalDifferential318.B_square
  simpa only [map_mul,map_sub,map_one,map_X,map_pow,B] using h

theorem B_constant : constantCoeff (B (K:=K))=1 := by
  rw [B,←coeff_zero_eq_constantCoeff_apply,coeff_map,FormalDifferential318.coeff_B,
    FormalDifferential318.b_zero,map_one]

@[expose] noncomputable def argument (D : K) : PowerSeries K := C D*X^4
@[expose] noncomputable def integral (D : K) : PowerSeries K := -X*(H (K:=K)).subst (argument D)
@[expose] noncomputable def differential (D : K) : PowerSeries K := (B (K:=K)).subst (argument D)
@[expose] noncomputable def branch (D : K) : PowerSeries K :=
  (1-argument D)*differential D

theorem argument_hasSubst (D : K) : HasSubst (argument D) :=
  HasSubst.of_constantCoeff_zero' (by simp [argument])

theorem subst_nat (D : K) (n : ℕ) : (n:PowerSeries K).subst (argument D)=n := by
  rw [←map_natCast C,subst_C]
  exact map_natCast C n

theorem substituted_ode (D : K) :
    4*((derivative (H (K:=K))).subst (argument D)*argument D)+(H (K:=K)).subst (argument D)=differential D := by
  have h := congrArg (fun f : PowerSeries K => f.subst (argument D)) (H_ode (K:=K))
  simpa only [subst_add (argument_hasSubst D),subst_mul (argument_hasSubst D),
    subst_X (argument_hasSubst D),show (4:PowerSeries K).subst (argument D)=4 from by simpa only [Nat.cast_ofNat] using subst_nat D 4,differential] using h

/-- The actual reciprocal series coefficients have the invariant differential. -/
theorem integral_derivative (D : K) : derivative (integral D)=-differential D := by
  have h := substituted_ode D
  simp only [integral,Derivation.leibniz,map_neg,derivative_X,derivative_subst (argument_hasSubst D)]
  simp only [argument,Derivation.leibniz,derivative_C,derivative_pow,derivative_X]
  norm_num
  simp only [argument] at h
  linear_combination -h

theorem differential_square (D : K) : (1-argument D)*(differential D)^2=1 := by
  have h := congrArg (fun f : PowerSeries K => f.subst (argument D)) (B_square (K:=K))
  simpa only [subst_mul (argument_hasSubst D),subst_sub (argument_hasSubst D),
    show (1:PowerSeries K).subst (argument D)=1 from by simpa only [Nat.cast_one] using subst_nat D 1,subst_X (argument_hasSubst D),
    subst_pow (argument_hasSubst D),differential] using h

theorem differential_branch (D : K) : differential D*branch D=1 := by
  dsimp only [branch]
  linear_combination differential_square D

theorem branch_square (D : K) : (branch D)^2=1-argument D := by
  dsimp only [branch]
  linear_combination (1-argument D)*differential_square D

theorem integral_differential (D : K) : derivative (integral D)*branch D = -1 := by
  rw [integral_derivative,neg_mul,differential_branch]



theorem integral_constant (D : K) : constantCoeff (integral D)=0 := by simp [integral]

theorem differential_constant (D : K) : constantCoeff (differential D)=1 := by
  change MvPowerSeries.constantCoeff ((B (K:=K)).subst (argument D))=1
  rw [constantCoeff_subst_of_constantCoeff_zero (by change constantCoeff (argument D)=0; simp [argument]) (B (K:=K)),B_constant]
  rfl

theorem branch_constant (D : K) : constantCoeff (branch D)=1 := by
  simp [branch,argument,differential_constant]

/-- The normalized reciprocal primitive is uniquely characterized by the
invariant differential on the constant-1 algebraic branch. -/
theorem integral_unique (D : K) (f : PowerSeries K) (h0 : constantCoeff f=0)
    (hd : derivative f*branch D = -1) : f=integral D := by
  apply derivative.ext
  · rw [integral_derivative]
    calc
      derivative f=derivative f*(differential D*branch D) := by rw [differential_branch,mul_one]
      _ = (derivative f*branch D)*differential D := by ring
      _ = -differential D := by rw [hd]; ring
  · rw [h0,integral_constant]


end GenericFormalDifferential318
#print axioms GenericFormalDifferential318.integral_differential
#print axioms GenericFormalDifferential318.integral_unique
