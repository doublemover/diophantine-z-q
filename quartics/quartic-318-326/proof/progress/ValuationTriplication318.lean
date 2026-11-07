module
public import InertThree318
public import ValuationAddition318
public section
namespace ValuationTriplication318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def psi (x : K) : K := 3*x^4-6*D*x^2-D^2
@[expose] noncomputable def phiRoot (x : K) : K := x^4+6*D*x^2-3*D^2

/-- Exact denominator and numerator valuations in the triplication formula
at the actual inert 3-place. -/
theorem polynomial_values (x : K) (a : ℤ) (hx : InertThree318.place x=a) (ha : a≤ -4) :
    InertThree318.place (psi x)=(4*a+2:ℤ) ∧
    InertThree318.place (phiRoot x)=(4*a:ℤ) := by
  let v := InertThree318.place
  have h2 : v (2:K)=0 := InertThree318.place_two
  have h3 : v (3:K)=(2:ℤ) := InertThree318.place_three
  have hD : v D=0 := InertThree318.place_D
  have h6 : v (6:K)=(2:ℤ) := by
    have he : (6:K)=2*3 := by norm_num
    rw [he,v.map_mul,h2,h3,zero_add]
  have hfirst : v (3*x^4)=(4*a+2:ℤ) := by
    rw [v.map_mul,v.map_pow,h3,hx]
    norm_cast
    simp only [nsmul_eq_mul]
    omega
  have hsecond : v (6*D*x^2)=(2*a+2:ℤ) := by
    rw [v.map_mul,v.map_mul,v.map_pow,h6,hD,hx]
    norm_cast
    simp only [nsmul_eq_mul]
    omega
  have hlast : v (D^2)=0 := by rw [v.map_pow,hD]; simp
  have hfour : v (x^4)=(4*a:ℤ) := by rw [v.map_pow,hx]; norm_cast
  have hthreeD : v (3*D^2)=(2:ℤ) := by rw [v.map_mul,hlast,h3,add_zero]
  constructor
  · change v (3*x^4-6*D*x^2-D^2)=_
    have hv : v (3*x^4-6*D*x^2)=(4*a+2:ℤ) := by
      rw [v.map_sub_eq_of_lt_left]
      · exact hfirst
      · rw [hfirst,hsecond]
        exact_mod_cast (show 4*a+2<2*a+2 by omega)
    rw [v.map_sub_eq_of_lt_left]
    · exact hv
    · rw [hv,hlast]
      exact_mod_cast (show 4*a+2<0 by omega)
  · change v (x^4+6*D*x^2-3*D^2)=_
    have hv : v (x^4+6*D*x^2)=(4*a:ℤ) := by
      rw [v.map_add_eq_of_lt_left]
      · exact hfour
      · rw [hfour,hsecond]
        exact_mod_cast (show 4*a<2*a+2 by omega)
    rw [v.map_sub_eq_of_lt_left]
    · exact hv
    · rw [hv,hthreeD]
      change ((4*a:ℤ):WithTop ℤ)<((2:ℤ):WithTop ℤ)
      exact_mod_cast (show 4*a<2 by omega)

theorem triplication_value (x : K) (a : ℤ) (hx : InertThree318.place x=a) (ha : a≤ -4) :
    InertThree318.place (x*(phiRoot x)^2/(psi x)^2)=(a-4:ℤ) := by
  obtain ⟨hp,hn⟩ := polynomial_values x a hx ha
  rw [InertThree318.place.map_div,InertThree318.place.map_mul,
    InertThree318.place.map_pow,InertThree318.place.map_pow,hx,hp,hn]
  norm_cast
  simp only [nsmul_eq_mul]
  omega

/-- Algebraic triplication in the actual elliptic group. The single excluded
case is exactly the displayed 3-division-polynomial zero. -/
theorem actual_tripling_x (x y : K) (h : E.Nonsingular x y) (hy : y≠0) (hp : psi x≠0) :
    ∃ (xx yy : K) (hh : E.Nonsingular xx yy),
      (Point.some x y h+Point.some x y h)+Point.some x y h=Point.some xx yy hh ∧
      xx=x*(phiRoot x)^2/(psi x)^2 := by
  have hc : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
  have hneg : y≠E.negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    have hz : 2*y=0 := by linear_combination hh
    exact (mul_ne_zero (by norm_num) hy) hz
  let m := (3*x^2-D)/(2*y)
  let xd := m^2-2*x
  let yd := m*(x-xd)-y
  have hm : E.slope x x y y=m := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [E,zero_mul,sub_zero,negY,sub_neg_eq_add]
    dsimp [m]
    congr 1 <;> ring
  have hdX : E.addX x x (E.slope x x y y)=xd := by
    rw [addX,hm]
    simp only [E,zero_mul,add_zero,sub_zero]
    dsimp [xd]
    ring
  have hdY : E.addY x x y (E.slope x x y y)=yd := by
    rw [addY,negAddY,negY,hdX,hm]
    simp only [E,zero_mul,sub_zero]
    dsimp [yd]
    ring
  have hd : E.Nonsingular xd yd := by
    have hh := nonsingular_add h h (fun hz => hneg hz.2)
    rwa [hdX,hdY] at hh
  have hdouble : Point.some x y h+Point.some x y h=Point.some xd yd hd := by
    rw [Point.add_self_of_Y_ne hneg]
    congr
  have hdiff : xd-x= -(psi x)/(4*y^2) := by
    dsimp [xd,m,psi]
    field_simp [hy]
    linear_combination -48*x*hc
  have hdx : xd≠x := by
    intro hh
    have hz := hdiff
    rw [hh,sub_self] at hz
    exact hp (neg_eq_zero.mp ((div_eq_zero_iff).mp hz.symm |>.resolve_right
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hy))))
  let ms := -m+8*y^3/(psi x)
  have hms : E.slope xd x yd y=ms := by
    rw [slope_of_X_ne hdx]
    dsimp [yd,ms]
    have hn : m*(x-xd)-y-y= -m*(xd-x)-2*y := by ring
    rw [hn,hdiff]
    field_simp [hy,hp]
    ring
  let xx := E.addX xd x (E.slope xd x yd y)
  let yy := E.addY xd x yd (E.slope xd x yd y)
  have hh : E.Nonsingular xx yy := nonsingular_add hd h (fun hz => hdx hz.1)
  refine ⟨xx,yy,hh,?_,?_⟩
  · rw [hdouble]
    exact Point.add_of_X_ne hdx
  · have hpoly : x*(psi x)^2-8*(3*x^2-D)*y^2*(psi x)+64*(y^2)^3=x*(phiRoot x)^2 := by
      rw [hc]
      dsimp [psi,phiRoot]
      ring
    have hid : ms^2-xd-x=
        (x*(psi x)^2-8*(3*x^2-D)*y^2*(psi x)+64*(y^2)^3)/(psi x)^2 := by
      dsimp [ms,xd,m]
      field_simp [hy,hp]
      ring
    change E.addX xd x (E.slope xd x yd y)=_
    rw [addX,hms]
    simp only [E,zero_mul,add_zero,sub_zero]
    rw [hid,hpoly]

end ValuationTriplication318
