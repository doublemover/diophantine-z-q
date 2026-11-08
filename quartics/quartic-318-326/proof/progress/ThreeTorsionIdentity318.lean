module
public import ShortTwoTorsion318
public section
noncomputable section
namespace ThreeTorsionIdentity318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (A B:R)

@[expose] def divisionPolynomial : R[X] :=
  3*X^4+C (6*A)*X^2+C (12*B)*X-C (A^2)

/-- Literal third-division polynomial derivative over every coefficient ring. -/
lemma derivative : (divisionPolynomial A B).derivative=
    C (12:R)*ShortTwoTorsion318.polynomial A B := by
  simp only [divisionPolynomial,ShortTwoTorsion318.polynomial,Polynomial.derivative_sub,
    Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow,
    Polynomial.derivative_X,Polynomial.derivative_C,Polynomial.derivative_ofNat,
    map_add,map_mul,map_pow,map_ofNat,map_natCast]
  ring

/-- Exact universal Bezout identity; no resultant or separability premise. -/
lemma bezout :
    (-C (4*A)-3*X^2)*divisionPolynomial A B+
      3*(C (7*A)*X+C (9*B)+3*X^3)*ShortTwoTorsion318.polynomial A B=
        C (4*A^3+27*B^2) := by
  simp only [divisionPolynomial,ShortTwoTorsion318.polynomial,map_add,map_mul,map_pow,map_ofNat]
  ring

/-- In the actual third-division quotient, the elliptic cubic value is a unit
at every smooth short-Weierstrass coefficient specialization. -/
lemma cubic_unit (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsUnit (AdjoinRoot.mk (divisionPolynomial A B) (ShortTwoTorsion318.polynomial A B)) := by
  have hh:=congrArg (AdjoinRoot.mk (divisionPolynomial A B)) (bezout A B)
  rw [map_add,map_mul,map_mul,AdjoinRoot.mk_self,mul_zero,zero_add,AdjoinRoot.mk_C] at hh
  have hu:IsUnit (AdjoinRoot.of (divisionPolynomial A B) (4*A^3+27*B^2)):=
    ((IsUnit.mul_iff.mp hD).2).map _
  rw [←hh,map_mul] at hu
  exact (IsUnit.mul_iff.mp hu).2

end ThreeTorsionIdentity318
