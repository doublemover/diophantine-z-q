module
public import OriginalGlobalCechRegularLifts318
public import OriginalGlobalP1Residue318
public section
noncomputable section
namespace OriginalGlobalCechOverlap318
open Polynomial OriginalSexticJetMarked318 OriginalGlobalCechRemainder318
open OriginalGlobalP1Residue318
variable {E K S : Type*} [Field E] [Field K] [Algebra E K] [CommRing S] [Algebra E S]
theorem rev_at_unit (p:E[X]) (n:ℕ) (h:p.natDegree≤n) (x:Sˣ) :
    aeval (↑x⁻¹:S) (reflect n p)=aeval (x:S) p*(↑x⁻¹:S)^n := by
  let inst : Invertible (x:S) := x.isUnit.invertible
  have eq : ⅟(x:S)=(↑x⁻¹:S) := invOf_eq_right_inv x.mul_inv
  have e:=eval₂_reflect_mul_pow (algebraMap E S) (x:S) n p h
  rw [eq] at e
  change aeval (↑x⁻¹:S) (reflect n p)*(x:S)^n=aeval (x:S) p at e
  rw [←e,mul_assoc,←mul_pow,x.mul_inv,one_pow,mul_one]

/-- Both components of the difference are computed via the ACTUAL overlap
v=x⁻¹, w=y/x³. Its horizontal vector is −yL/2 times (2y,F′);
this extends across the branch points with no inversion of y or F′. -/
theorem difference (J : Certificate E K) (q:E[X])
    (hq : J.G-J.remainder 0*J.F.derivative=J.F*q)
    (x:Sˣ) (y c:S) (hy:y^2=aeval (x:S) J.F) (hc:2*c=1) :
    let z: S := x
    let v: S := ↑x⁻¹
    let w:=y*v^3
    let l:=aeval z (A J)*v^3
    let dv:=aeval v (reflect 5 (P J))
    let dw:=c*w*aeval v (reflect 4 (Qstar J q))
    (-aeval z (J.remainder 0))-(-z^2*dv)=(-c*y*l)*(2*y) ∧
    c*y*aeval z q-(z^3*dw-3*y*z*dv)=(-c*y*l)*aeval z J.F.derivative := by
  dsimp only
  rw [rev_at_unit (P J) 5 (small_step J 2),rev_at_unit (Qstar J q) 4 (Qstar_small J q hq)]
  rw [Qstar,P_eq]
  simp only [map_add,map_sub,map_mul,map_pow,aeval_X,map_ofNat]
  have H:=x.mul_inv
  constructor <;> grind

@[expose] def form (J : Certificate E K) (k:Fin 3) : LaurentPolynomial E :=
  -(LaurentPolynomial.T (k:ℕ)*toLaurent (A J)*LaurentPolynomial.T (-3))

/-- The pullback class directly produced by the relative vector above reads
−x^k A(x)/x³ dx on every test-algebra unit. -/
theorem form_eval (J:Certificate E K) (k:Fin 3) (x:Sˣ) :
    LaurentPolynomial.eval₂ (algebraMap E S) x (form J k)=
      -((x:S)^(k:ℕ)*aeval (x:S) (A J)*(↑x⁻¹:S)^3) := by
  rw [form,map_neg,map_mul,map_mul,LaurentPolynomial.eval₂_T_n,LaurentPolynomial.eval₂_toLaurent]
  have e:=LaurentPolynomial.eval₂_T_neg_n (algebraMap E S) x 3
  norm_num only [Nat.cast_ofNat] at e
  rw [e]
  rfl

theorem residue (J : Certificate E K) (k:Fin 3) :
    res (form J k)= -coef J k := by
  have H (a:E) (k n:ℤ) :
      LaurentPolynomial.T k*(LaurentPolynomial.C a*LaurentPolynomial.T n)*LaurentPolynomial.T (-3)=
        mon a (k+n-3) := by
    rw [mon,mul_left_comm,←LaurentPolynomial.T_add,LaurentPolynomial.mul_T_assoc]
    rfl
  unfold form A
  simp only [map_add,map_mul,map_pow,toLaurent_C,toLaurent_X,LaurentPolynomial.T_pow,mul_add,add_mul]
  have HC (a:E) (k:ℤ) : LaurentPolynomial.T k*LaurentPolynomial.C a*LaurentPolynomial.T (-3)=
      mon a (k+0-3) := by simpa only [LaurentPolynomial.T_zero,mul_one] using H a k 0
  simp only [H,HC,res_neg,res_add,res_mon]
  fin_cases k <;> norm_num
end OriginalGlobalCechOverlap318
#print axioms OriginalGlobalCechOverlap318.difference
#print axioms OriginalGlobalCechOverlap318.residue
