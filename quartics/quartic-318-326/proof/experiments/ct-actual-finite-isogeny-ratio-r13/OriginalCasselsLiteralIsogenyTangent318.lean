module
public import OriginalCasselsLiteralIsogenySecant318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
public section

noncomputable section

namespace OriginalCasselsLiteralIsogenyTangent318

open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318
open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyExceptional318
open OriginalCasselsLiteralIsogenySecant318 WeierstrassCurve.Affine

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private theorem ne_neg_self {y : F} (hy : y ≠ 0) : y ≠ -y := by
  intro h
  have h' : 2*y=0 := by linear_combination h
  exact mul_ne_zero (by norm_num : (2:F) ≠ 0) hy h'

/-- The literal derivative numerator is transported by the same oriented
slope as the secant. This is proved by clearing the original denominators
and the two exact source equations, not by continuity of an unknown map. -/
private theorem oriented_tangent (n x y m c : F) (hx : x ≠ 0) (hc : c ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n))
    (hd : 2*m*y=3*x^2+4*n*x-3*n^2) (hC : c=y-m*x) :
    3*(Ximage n x)^2-8*n*(Ximage n x)+16*n^2 =
      2*(Yimage n x y)*imageSlope n m c := by
  have hd' : 2*m*(x^3+2*n*x^2-3*n^2*x)=(3*x^2+4*n*x-3*n^2)*y := by
    linear_combination -2*m*he+y*hd
  have hclear :
      (x^2*c)*(3*(Ximage n x)^2-8*n*(Ximage n x)+16*n^2
        -2*(Yimage n x y)*imageSlope n m c) =
       (x^2+3*n^2)*(m*x-y)*(2*m*y-(3*x^2+4*n*x-3*n^2)) +
        6*n^2*(2*m*(x^3+2*n*x^2-3*n^2*x)-(3*x^2+4*n*x-3*n^2)*y) := by
    change (x^2*c)*(3*(x+2*n-3*n^2/x)^2-8*n*(x+2*n-3*n^2/x)+16*n^2
      -2*(y+3*n^2*y/x^2)*(m+3*n^2/c)) = _
    have hX : x*(x+2*n-3*n^2/x)=x*(x+2*n)-3*n^2 := by
      calc
        _ = x*(x+2*n)-(3*n^2/x)*x := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hx]
    have hY : x^2*(y+3*n^2*y/x^2)=x^2*y+3*n^2*y := by
      calc
        _ = x^2*y+(3*n^2*y/x^2)*x^2 := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (pow_ne_zero 2 hx)]
    have hS : c*(m+3*n^2/c)=c*m+3*n^2 := by
      calc
        _ = c*m+(3*n^2/c)*c := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hc]
    calc
      _ = c*(3*(x*(x+2*n-3*n^2/x))^2-8*n*x*(x*(x+2*n-3*n^2/x))+16*n^2*x^2)
          -2*(x^2*(y+3*n^2*y/x^2))*(c*(m+3*n^2/c)) := by ring
      _ = _ := by rw [hX,hY,hS,hC]; ring
  simp only [hd,hd',sub_self,mul_zero,add_zero] at hclear
  exact sub_eq_zero.mp ((mul_eq_zero.mp hclear).resolve_left
    (mul_ne_zero (pow_ne_zero _ hx) hc))

/-- All native doubles, including y=0 and the tangent passing through the
omitted root. In the ordinary case the target tangent is nonvertical
because its ordinate is proved nonzero from the same intercept. -/
theorem actual_add_self (n x y : F) (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    literalMap n hn (point n x y hn he+point n x y hn he)=
      literalMap n hn (point n x y hn he)+literalMap n hn (point n x y hn he) := by
  by_cases hy : y=0
  · have hP : -point n x y hn he=point n x y hn he := by
      rw [actual_point_neg]
      simp only [hy,neg_zero]
    simpa only [hP] using actual_add_vertical n hn (point n x y hn he)
  · let m := (3*x^2+4*n*x-3*n^2)/(2*y)
    let c := y-m*x
    let x₃ := m^2-2*n-x-x
    have hsrc : y ≠ (curve n).toAffine.negY x y := by rw [curve_negY]; exact ne_neg_self hy
    have hnv : ¬(x=x ∧ y=(curve n).toAffine.negY x y) := fun h => hsrc h.2
    have hm : (curve n).toAffine.slope x x y y=m := by
      rw [slope_of_Y_ne rfl hsrc,curve_negY]
      change (3*x^2+2*(2*n)*x+(-3*n^2)-0*y)/(y-(-y))=m
      dsimp [m]
      congr 1 <;> ring
    have hd : 2*m*y=3*x^2+4*n*x-3*n^2 := by
      have hh : (2:F)*y ≠ 0 := mul_ne_zero (by norm_num) hy
      dsimp [m]
      field_simp [hh,hy] <;> ring
    by_cases hc₀ : c=0
    · exact actual_add_of_zero_intercept n x y x y m x₃ hn he he hx hx hnv hm rfl
        (hc₀.symm.trans (show c=y-m*x from rfl))
    · have hc' : 2*y*c = -x*(x^2+3*n^2) := by
        dsimp [c]
        linear_combination 2*he-x*hd
      have hq : x^2+3*n^2 ≠ 0 := by
        intro h
        have hh : (2:F)*y*c=0 := by rw [hc',h,mul_zero]
        exact mul_ne_zero (mul_ne_zero (by norm_num) hy) hc₀ hh
      have hY : Yimage n x y ≠ 0 := by
        have hEq : Yimage n x y = y*(x^2+3*n^2)/x^2 := by
          change y+3*n^2*y/x^2=y*(x^2+3*n^2)/x^2
          field_simp [hx] <;> ring
        rw [hEq]
        exact div_ne_zero (mul_ne_zero hy hq) (pow_ne_zero _ hx)
      have htar : Yimage n x y ≠ (targetModel n).toAffine.negY (Ximage n x) (Yimage n x y) := by
        rw [target_negY]
        exact ne_neg_self hY
      apply actual_add_of_image_slope n x y x y m x₃ c hn he he hx hx hc₀ hnv hm rfl rfl
        (fun h => htar h.2)
      rw [slope_of_Y_ne rfl htar,target_negY]
      calc
        _ = (3*(Ximage n x)^2-8*n*(Ximage n x)+16*n^2)/(2*(Yimage n x y)) := by
          change (3*(Ximage n x)^2+2*(-4*n)*(Ximage n x)+16*n^2-0*(Yimage n x y))/
            ((Yimage n x y)-(-(Yimage n x y)))=_
          congr 1 <;> ring
        _ = _ := by
          apply (div_eq_iff (mul_ne_zero (by norm_num : (2:F)≠0) hY)).2
          rw [oriented_tangent n x y m c hx hc₀ he hd rfl]
          ring

end OriginalCasselsLiteralIsogenyTangent318

#print axioms OriginalCasselsLiteralIsogenyTangent318.actual_add_self
