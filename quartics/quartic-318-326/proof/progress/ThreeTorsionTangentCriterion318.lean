module
public import ThreeTorsionFunctor318
public section
noncomputable section
namespace ThreeTorsionTangentCriterion318
set_option maxHeartbeats 0
variable {S:Type*} [CommRing S]

/-- The third-division equation is exactly the tangent doubling/negation
condition over every commutative ring, including rings with nilpotents. -/
theorem criterion (a b x y l:S) (he:y^2=x^3+a*x+b)
    (hl:l*(2*y)=3*x^2+a) (hu:IsUnit (2*y)) :
    3*x^4+6*a*x^2+12*b*x-a^2=0 ↔
      l^2-x-x=x ∧ l*(x-(l^2-x-x))-y= -y := by
  have hid:(2*y)^2*(l^2-3*x)=
      (l*(2*y)-(3*x^2+a))*(l*(2*y)+(3*x^2+a))-
      (3*x^4+6*a*x^2+12*b*x-a^2)-12*x*(y^2-(x^3+a*x+b)):=by ring
  rw [hl,he,sub_self,sub_self,zero_mul,mul_zero,sub_zero,zero_sub] at hid
  constructor
  · intro hp
    have hs:l^2=3*x:=by
      apply sub_eq_zero.mp
      apply ((hu.pow 2).mul_right_eq_zero).mp
      rw [hid,hp,neg_zero]
    constructor <;> rw [hs] <;> ring
  · rintro ⟨hx,_⟩
    have hs:l^2-3*x=0:=by linear_combination hx
    rw [hs,mul_zero] at hid
    exact neg_eq_zero.mp hid.symm

/-- Coefficients are transported from the original base. No reduction to
field-valued points is used. -/
theorem normalized_criterion {R:Type*} [CommRing R] [Algebra R S]
    (A B:R) [Invertible (3:R)] (x y l:S)
    (he:y^2=x^3+algebraMap R S A*x+algebraMap R S B)
    (hl:l*(2*y)=3*x^2+algebraMap R S A) (hu:IsUnit (2*y)) :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S) x=0 ↔
      l^2-x-x=x ∧ l*(x-(l^2-x-x))-y= -y := by
  rw [ThreeTorsionFunctor318.normalized_eval_iff]
  simpa only [ThreeTorsionIdentity318.divisionPolynomial,Polynomial.eval₂_sub,
    Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,Polynomial.eval₂_ofNat,map_mul,map_pow,map_ofNat]
    using criterion (algebraMap R S A) (algebraMap R S B) x y l he hl hu

end ThreeTorsionTangentCriterion318
