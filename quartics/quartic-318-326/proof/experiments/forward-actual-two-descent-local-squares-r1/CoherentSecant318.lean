module
public import CoherentSecantPolynomial318
public import CoherentMultipleCharts318
public section
noncomputable section
namespace CoherentSecant318
open ConcreteG8Domain (K D)
open LocalGenerator318 (E)
open CoherentMultipleCharts318 (u v denominator_ne)
open CoherentSecantPolynomial318 (rawX rawY)
open WeierstrassCurve.Affine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma rational_identity (x y a b : K)
    (hc : y^2=x^3-D*x) (hd : b^2=a^3-D*a)
    (hr : (rawX x y a b)^2+D*(a-x)^4≠0) :
    (2*rawY x y a b*(a-x)/((rawX x y a b)^2+D*(a-x)^4))*
      (1+D*(2*y/(x^2+D))^2*(2*b/(a^2+D))^2)=
    (2*y/(x^2+D))*((a^4-6*D*a^2+D^2)/(a^2+D)^2)-
      (2*b/(a^2+D))*((x^4-6*D*x^2+D^2)/(x^2+D)^2) := by
  have hp := CoherentSecantPolynomial318.secant_identity D x y a b hc hd
  field_simp [denominator_ne x,denominator_ne a,hr]
  apply (div_eq_iff (show (rawX x y a b)^2+(a-x)^4*D≠0 by simpa only [mul_comm] using hr)).mpr
  linear_combination (1/2:K)*hp

/-- The rational duplication chart respects actual subtraction whenever the
finite half-point abscissae differ. It is an oriented u-identity, not a square. -/
theorem finite_u_sub (x y a b : K) (hx : E.Nonsingular x y) (ha : E.Nonsingular a b)
    (hne : x≠a) :
    u (Point.some x y hx-Point.some a b ha)*
      (1+D*(u (Point.some x y hx))^2*(u (Point.some a b ha))^2)=
      u (Point.some x y hx)*v (Point.some a b ha)-
        u (Point.some a b ha)*v (Point.some x y hx) := by
  have hd : a-x≠0 := sub_ne_zero.mpr hne.symm
  have hs : E.slope x a y (E.negY a b)=(-b-y)/(a-x) := by
    rw [slope_of_X_ne hne]
    simp only [negY,E,zero_mul,sub_zero]
    field_simp [hd,sub_ne_zero.mpr hne]
    ring
  have hX : E.addX x a (E.slope x a y (E.negY a b))=
      rawX x y a b/(a-x)^2 := by
    rw [addX,hs]
    simp only [E,zero_mul,sub_zero]
    dsimp [rawX]
    field_simp [hd]
    ring
  have hY : E.addY x a y (E.slope x a y (E.negY a b))=
      rawY x y a b/(a-x)^3 := by
    rw [addY,negAddY,negY,hX,hs]
    simp only [E,zero_mul,sub_zero]
    dsimp [rawY]
    field_simp [hd]
    ring
  have hr : (rawX x y a b)^2+D*(a-x)^4≠0 := by
    have he : (rawX x y a b)^2+D*(a-x)^4=
        ((rawX x y a b/(a-x)^2)^2+D)*(a-x)^4 := by field_simp [hd]
    rw [he]
    exact mul_ne_zero (denominator_ne _) (pow_ne_zero _ hd)
  have hc : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using hx.1
  have hc' : b^2=a^3-D*a := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using ha.1
  rw [sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hne]
  change (2*E.addY x a y (E.slope x a y (E.negY a b))/
    ((E.addX x a (E.slope x a y (E.negY a b)))^2+D))*_=_
  rw [hX,hY]
  have he : 2*(rawY x y a b/(a-x)^3)/((rawX x y a b/(a-x)^2)^2+D)=
      2*rawY x y a b*(a-x)/((rawX x y a b)^2+D*(a-x)^4) := by
    field_simp [hd,hr,denominator_ne (rawX x y a b/(a-x)^2)]
  rw [he]
  exact rational_identity x y a b hc hc' hr

end CoherentSecant318
