module
public import HCoefficients318
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Data.Nat.Choose.Central
public section
namespace FormalDifferential318
open PowerSeries
open scoped PowerSeries

@[expose] def b (n : ℕ) : ℚ := (n.centralBinom:ℚ)/4^n
@[expose] noncomputable def B : PowerSeries ℚ := PowerSeries.mk b

@[simp] theorem coeff_B (n : ℕ) : coeff n B=b n := coeff_mk _ _
@[simp] theorem b_zero : b 0=1 := by norm_num [b]

theorem b_recurrence (n : ℕ) : 2*((n:ℚ)+1)*b (n+1)=(2*n+1)*b n := by
  have h : ((n:ℚ)+1)*(n+1).centralBinom=2*(2*n+1)*n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  simp only [b,pow_succ]
  field_simp
  linear_combination 2*h

/-- The generating function for the central binomial coefficients satisfies
its exact formal differential equation. -/
theorem B_ode : 2*(1-X)*derivative B=B := by
  have hr : 2*(1-X)*derivative B=2*derivative B-2*(derivative B*X) := by ring
  rw [hr]
  ext n
  cases n with
  | zero =>
    simp only [map_sub,coeff_ofNat_mul,coeff_zero_mul_X,coeff_derivative,coeff_B]
    norm_num [b,Nat.centralBinom]
  | succ n =>
    simp only [map_sub,coeff_ofNat_mul,coeff_succ_mul_X,coeff_derivative,coeff_B]
    have h := b_recurrence (n+1)
    push_cast at h ⊢
    linear_combination h

theorem B_constant : constantCoeff B=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,coeff_B,b_zero]

/-- Exact inverse-square-root identity, not a finite truncation. -/
theorem B_square : (1-X)*B^2=1 := by
  apply derivative.ext
  · have h := B_ode
    simp only [map_mul,map_sub,derivative_one,derivative_X,derivative_pow]
    norm_num
    linear_combination B*h
  · simp [B_constant]


@[expose] noncomputable def H : PowerSeries ℚ := PowerSeries.mk HCoefficients318.coefficient
@[simp] theorem coeff_H (n : ℕ) : coeff n H=HCoefficients318.coefficient n := coeff_mk _ _

theorem coefficient_integral (n : ℕ) :
    HCoefficients318.coefficient n*(4*(n:ℚ)+1)=b n := by
  have hn : (4*(n:ℚ)+1)≠0 := by positivity
  simp only [HCoefficients318.coefficient,b,Nat.centralBinom,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one]
  field_simp

/-- Exact coefficient identity for the integrated H series. -/
theorem H_ode : 4*(derivative H*X)+H=B := by
  ext n
  cases n with
  | zero =>
    simp only [map_add,coeff_ofNat_mul,coeff_zero_mul_X,coeff_H,coeff_B]
    norm_num [HCoefficients318.coefficient,b,Nat.centralBinom]
  | succ n =>
    simp only [map_add,coeff_ofNat_mul,coeff_succ_mul_X,coeff_derivative,coeff_H,coeff_B]
    have h := coefficient_integral (n+1)
    push_cast at h ⊢
    linear_combination h

@[expose] noncomputable def argument (D : ℚ) : PowerSeries ℚ := C D*X^4
@[expose] noncomputable def integral (D : ℚ) : PowerSeries ℚ := -X*H.subst (argument D)
@[expose] noncomputable def differential (D : ℚ) : PowerSeries ℚ := B.subst (argument D)
@[expose] noncomputable def branch (D : ℚ) : PowerSeries ℚ :=
  (1-argument D)*differential D

theorem argument_hasSubst (D : ℚ) : HasSubst (argument D) :=
  HasSubst.of_constantCoeff_zero' (by simp [argument])

theorem subst_nat (D : ℚ) (n : ℕ) : (n:PowerSeries ℚ).subst (argument D)=n := by
  rw [←map_natCast C,subst_C]
  exact map_natCast C n

theorem substituted_ode (D : ℚ) :
    4*((derivative H).subst (argument D)*argument D)+H.subst (argument D)=differential D := by
  have h := congrArg (fun f : PowerSeries ℚ => f.subst (argument D)) H_ode
  simpa only [subst_add (argument_hasSubst D),subst_mul (argument_hasSubst D),
    subst_X (argument_hasSubst D),show (4:PowerSeries ℚ).subst (argument D)=4 from subst_nat D 4,differential] using h

/-- The actual reciprocal series coefficients have the invariant differential. -/
theorem integral_derivative (D : ℚ) : derivative (integral D)=-differential D := by
  have h := substituted_ode D
  simp only [integral,Derivation.leibniz,map_neg,derivative_X,derivative_subst (argument_hasSubst D)]
  simp only [argument,Derivation.leibniz,derivative_C,derivative_pow,derivative_X]
  norm_num
  simp only [argument] at h
  linear_combination -h

theorem differential_square (D : ℚ) : (1-argument D)*(differential D)^2=1 := by
  have h := congrArg (fun f : PowerSeries ℚ => f.subst (argument D)) B_square
  simpa only [subst_mul (argument_hasSubst D),subst_sub (argument_hasSubst D),
    show (1:PowerSeries ℚ).subst (argument D)=1 from subst_nat D 1,subst_X (argument_hasSubst D),
    subst_pow (argument_hasSubst D),differential] using h

theorem differential_branch (D : ℚ) : differential D*branch D=1 := by
  dsimp only [branch]
  linear_combination differential_square D

theorem branch_square (D : ℚ) : (branch D)^2=1-argument D := by
  dsimp only [branch]
  linear_combination (1-argument D)*differential_square D

theorem integral_differential (D : ℚ) : derivative (integral D)*branch D = -1 := by
  rw [integral_derivative,neg_mul,differential_branch]



theorem integral_constant (D : ℚ) : constantCoeff (integral D)=0 := by simp [integral]

theorem differential_constant (D : ℚ) : constantCoeff (differential D)=1 := by
  change MvPowerSeries.constantCoeff (B.subst (argument D))=1
  rw [constantCoeff_subst_of_constantCoeff_zero (by change constantCoeff (argument D)=0; simp [argument]) B,B_constant]
  rfl

theorem branch_constant (D : ℚ) : constantCoeff (branch D)=1 := by
  simp [branch,argument,differential_constant]

/-- The normalized reciprocal primitive is uniquely characterized by the
invariant differential on the constant-1 algebraic branch. -/
theorem integral_unique (D : ℚ) (f : PowerSeries ℚ) (h0 : constantCoeff f=0)
    (hd : derivative f*branch D = -1) : f=integral D := by
  apply derivative.ext
  · rw [integral_derivative]
    calc
      derivative f=derivative f*(differential D*branch D) := by rw [differential_branch,mul_one]
      _ = (derivative f*branch D)*differential D := by ring
      _ = -differential D := by rw [hd]; ring
  · rw [h0,integral_constant]


end FormalDifferential318
#print axioms FormalDifferential318.B_ode
#print axioms FormalDifferential318.B_square

#print axioms FormalDifferential318.integral_derivative
#print axioms FormalDifferential318.integral_differential
#print axioms FormalDifferential318.branch_square

#print axioms FormalDifferential318.integral_unique
