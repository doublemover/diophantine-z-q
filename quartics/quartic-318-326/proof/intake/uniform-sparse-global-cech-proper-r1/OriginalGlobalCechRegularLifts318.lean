module
public import OriginalGlobalCechRemainder318
public import OriginalBranchCechCalculus318
public section
noncomputable section
namespace OriginalGlobalCechRegularLifts318
open Polynomial OriginalGlobalCechRemainder318 OriginalSexticJetMarked318
variable {E K : Type*} [Field E] [Field K] [Algebra E K]

theorem reflect_derivative (F : E[X]) (hf : F.natDegree≤6) :
    reflect 5 (C 6*F-X*F.derivative)=(reflect 6 F).derivative := by
  ext i
  by_cases hi : i≤5
  · have hd (n:ℕ) : (X*F.derivative).coeff n = F.coeff n*(n:E) := by
      cases n with
      | zero => rw [coeff_X_mul_zero,Nat.cast_zero,mul_zero]
      | succ n => rw [coeff_X_mul,coeff_derivative,Nat.cast_succ]
    rw [coeff_derivative,coeff_reflect,coeff_reflect,revAt_le hi,
      revAt_le (by omega : i+1 ≤ 6),coeff_sub,coeff_C_mul,hd]
    have e : 6-(i+1)=5-i := by omega
    rw [e,Nat.cast_sub hi]
    push_cast
    ring
  · have hi' : 5 < i := by omega
    have h6 : 6 < i+1 := by omega
    have hs:=reciprocal_derivative_small F hf
    rw [coeff_reflect,revAt_eq_self_of_lt hi',
        coeff_eq_zero_of_natDegree_lt (hs.trans_lt hi'),coeff_derivative,coeff_reflect,
        revAt_eq_self_of_lt h6,coeff_eq_zero_of_natDegree_lt (hf.trans_lt h6),zero_mul]

/-- The affine tangent identity is an identity of reciprocal POLYNOMIALS,
including at v=0, not a rational function regularity hypothesis. -/
theorem reciprocal_equation (J : Certificate E K) (q : E[X])
    (hq : J.G-J.remainder 0*J.F.derivative=J.F*q) :
    reflect 6 J.F*reflect 4 (Qstar J q) - (reflect 6 J.F).derivative*reflect 5 (P J)=
      reflect 6 J.G := by
  have h:=congrArg (reflect 10) (Qstar_eq J q hq)
  have hf:=(sextic J).1.le
  have r0:= reflect_mul J.F (Qstar J q) hf (Qstar_small J q hq)
  have r1:= reflect_mul (X^4 : E[X]) J.G (show (X^4 : E[X]).natDegree≤4 by rw [natDegree_X_pow])
    J.true_jet_degree
  have r2:= reflect_mul (C 6*J.F-X*J.F.derivative) (P J) (reciprocal_derivative_small _ hf)
    (small_step J 2)
  have r3 : reflect 4 ((X:E[X])^4)=1 := by rw [reflect_monomial,revAt_le (le_refl 4),Nat.sub_self,pow_zero]
  rw [show 10=6+4 by rfl,r0] at h
  rw [reflect_add,show 6+4=4+6 by rfl,r1, r3,one_mul,show 4+6=5+5 by rfl,r2,reflect_derivative J.F hf] at h
  linear_combination h

variable {S : Type*} [CommRing S] [Algebra E S]
/-- Construct sections of the actual square-zero deformation on BOTH standard
affine charts, over an arbitrary test algebra and every nilpotent of square 0.
The scalar c is 1/2; q is obtained without denominators at roots or infinity. -/
theorem regular_lifts (J : Certificate E K) (q : E[X])
    (hq : J.G-J.remainder 0*J.F.derivative=J.F*q)
    (x y v w ε c : S) (hy : y^2=aeval x J.F) (hw : w^2=aeval v (reflect 6 J.F))
    (hc : 2*c=1) (hε : ε^2=0) :
    (y+ε*(c*aeval x q*y))^2 = aeval (x+ε*(-aeval x (J.remainder 0))) J.F+
      ε*aeval (x+ε*(-aeval x (J.remainder 0))) J.G ∧
    (w+ε*(c*aeval v (reflect 4 (Qstar J q))*w))^2 =
      aeval (v+ε*aeval v (reflect 5 (P J))) (reflect 6 J.F)+
      ε*aeval (v+ε*aeval v (reflect 5 (P J))) (reflect 6 J.G) := by
  constructor
  · apply OriginalBranchCechCalculus318.genuine_lift _ _ _ _ _ _ _ hε hy
    have e:=congrArg (aeval x) hq
    simp only [map_sub,map_mul] at e
    linear_combination -e+(aeval x q)*hy+(y^2*aeval x q)*hc
  · apply OriginalBranchCechCalculus318.genuine_lift _ _ _ _ _ _ _ hε hw
    have e:=congrArg (aeval v) (reciprocal_equation J q hq)
    simp only [map_sub,map_mul] at e
    linear_combination e+(aeval v (reflect 4 (Qstar J q)))*hw+
      (w^2*aeval v (reflect 4 (Qstar J q)))*hc
end OriginalGlobalCechRegularLifts318
#print axioms OriginalGlobalCechRegularLifts318.regular_lifts
