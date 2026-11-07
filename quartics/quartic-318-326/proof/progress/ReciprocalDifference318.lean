module
public import PrimaryFormal318
public import CompressedGlobal318
public section
namespace ReciprocalDifference318
open ConcreteG8Domain (K pair)
open CompressedOrientation318 CompressedPoint318 CompressedGlobal318 PrimaryFormal318
open WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
noncomputable section

/-- Every K-rational reciprocal quartic ordinate is nonzero, globally. -/
theorem ordinate_ne (u v : K) (hc : v^2=1-D*u^4) : v≠0 := by
  intro hv
  rw [hv,zero_pow (by decide : 2≠0)] at hc
  apply norm_square_obstruction (u^2) (QuadraticAlgebra.norm u) (map_pow _ _ _)
  linear_combination hc

/-- The actual finite difference abscissa in the nonidentity branches. -/
theorem difference_x (u v t w h : K) (hu : u≠0) (ht : t≠0)
    (hcU : v^2=1-D*u^4) (hcV : w^2=1-D*t^4)
    (hd : t^2-u^2≠0) (hh : (t^2-u^2)*h=u*w+t*v) :
    E.addX (1/u^2) (1/t^2)
      (E.slope (1/u^2) (1/t^2) (v/u^3) (E.negY (1/t^2) (w/t^3)))=h^2 := by
  have hx : (1:K)/u^2≠1/t^2 := by
    intro he
    field_simp [hu,ht] at he
    apply hd
    linear_combination he
  rw [addX,slope_of_X_ne hx]
  simp only [E,negY,zero_mul,mul_zero,sub_zero,add_zero,sub_neg_eq_add]
  have hroot : h=(u*w+t*v)/(t^2-u^2) :=
    (eq_div_iff hd).mpr (by simpa [mul_comm] using hh)
  rw [hroot]
  field_simp [hu,ht,hd]
  linear_combination (t^2-u^2)*(t^4*hcU-u^4*hcV)

/-- No denominator except the actual source's difference guard is imposed.
Both reciprocal identity charts remain included. -/
theorem actual_difference (u v t w h : K)
    (hcU : v^2=1-D*u^4) (hcV : w^2=1-D*t^4)
    (hd : t^2-u^2≠0) (hh : (t^2-u^2)*h=u*w+t*v) :
    ∃(y:K)(hn:E.Nonsingular (h^2) y),
      point u v (ordinate_ne u v hcU) hcU-point t w (ordinate_ne t w hcV) hcV=
        Point.some (h^2) y hn := by
  have hv := ordinate_ne u v hcU
  have hw := ordinate_ne t w hcV
  by_cases hu : u=0
  · have ht : t≠0 := by intro ht; simp [hu,ht] at hd
    have hv2 : v^2=1 := by simpa [hu] using hcU
    have hr : h=v/t := by
      apply (eq_div_iff ht).mpr
      rw [hu] at hh
      have he : t*(h*t-v)=0 := by linear_combination hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ht)
    have hx : h^2=1/t^2 := by rw [hr,div_pow,hv2]
    have hn := (nonsingular_neg (1/t^2) (w/t^3)).mpr (reciprocal_nonsingular t w ht hw hcV)
    rw [←hx] at hn
    refine ⟨E.negY (h^2) (w/t^3),hn,?_⟩
    simp only [point,dite_eq_left hu,dite_eq_right ht,zero_sub,Point.neg_some]
    simp only [hx]
  · by_cases ht : t=0
    · have hw2 : w^2=1 := by simpa [ht] using hcV
      have hr : h= -w/u := by
        apply (eq_div_iff hu).mpr
        rw [ht] at hh
        have he : u*(h*u+w)=0 := by linear_combination -hh
        have hz := (mul_eq_zero.mp he).resolve_left hu
        linear_combination hz
      have hx : h^2=1/u^2 := by rw [hr,div_pow,neg_sq,hw2]
      have hn := reciprocal_nonsingular u v hu hv hcU
      rw [←hx] at hn
      refine ⟨v/u^3,hn,?_⟩
      simp only [point,dite_eq_right hu,dite_eq_left ht,sub_zero,hx]
    · have hx : (1:K)/u^2≠1/t^2 := by
        intro he
        field_simp [hu,ht] at he
        apply hd
        linear_combination he
      have hU := reciprocal_nonsingular u v hu hv hcU
      have hV := (nonsingular_neg (1/t^2) (w/t^3)).mpr (reciprocal_nonsingular t w ht hw hcV)
      let l := E.slope (1/u^2) (1/t^2) (v/u^3) (E.negY (1/t^2) (w/t^3))
      let yy := E.addY (1/u^2) (1/t^2) (v/u^3) l
      have hn := nonsingular_add hU hV (fun he => hx he.1)
      have hxx := difference_x u v t w h hu ht hcU hcV hd hh
      rw [hxx] at hn
      refine ⟨yy,hn,?_⟩
      simp only [point,dite_eq_right hu,dite_eq_right ht,sub_eq_add_neg,Point.neg_some]
      rw [Point.add_of_X_ne hx]
      simp only [hxx,yy,l]

end
end ReciprocalDifference318
