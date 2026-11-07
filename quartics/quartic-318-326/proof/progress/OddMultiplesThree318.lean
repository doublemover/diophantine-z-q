module
public import GeneratorMultiplesThree318
public section
namespace OddMultiplesThree318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine ThreeGroupSteps318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A formal point plus an integral point with unit abscissa again has unit
abscissa. The slope cancellation is resolved by the same exact numerator. -/
theorem unit_add_value (x1 y1 x2 y2 : K) (a b c : ℤ)
    (hx1 : InertThree318.place x1=a) (hy1 : InertThree318.place y1=b)
    (hx2 : InertThree318.place x2=0) (hy2 : InertThree318.place y2=c) (hc0 : 0≤c)
    (hc1 : y1^2=x1^3-D*x1) (hc2 : y2^2=x2^3-D*x2) (ha : a<0) :
    InertThree318.place (((y1-y2)/(x1-x2))^2-x1-x2)=0 := by
  let v := InertThree318.place
  have hD : v D=0 := InertThree318.place_D
  have h2 : v (2:K)=0 := InertThree318.place_two
  have hb := ValuationAddition318.ordinate_value v D x1 y1 a b hD hx1 hy1 hc1 ha
  have hxx : x1-x2≠0 := by
    intro h
    have hh := congrArg v (sub_eq_zero.mp h)
    rw [hx1,hx2] at hh
    have hh' : a=0 := by exact_mod_cast hh
    omega
  have hden : v ((x1-x2)^2)=(2*a:ℤ) := by
    rw [v.map_pow,v.map_sub_eq_of_lt_left]
    · rw [hx1]; norm_cast
    · rw [hx1,hx2]; exact_mod_cast ha
  have hlead : v (x1^2*x2)=(2*a:ℤ) := by
    rw [v.map_mul,v.map_pow,hx1,hx2,add_zero]; norm_cast
  have ht1 : ((2*a:ℤ):WithTop ℤ)<v (x1*x2^2) := by
    rw [v.map_mul,v.map_pow,hx1,hx2]
    simp only [smul_zero,add_zero]
    exact_mod_cast (show 2*a<a by omega)
  have ht2 : ((2*a:ℤ):WithTop ℤ)<v (-(D*x1)) := by
    rw [v.map_neg,v.map_mul,hD,hx1,zero_add]
    exact_mod_cast (show 2*a<a by omega)
  have ht3 : ((2*a:ℤ):WithTop ℤ)<v (-(D*x2)) := by
    rw [v.map_neg,v.map_mul,hD,hx2,zero_add]
    exact_mod_cast (show 2*a<0 by omega)
  have ht4 : ((2*a:ℤ):WithTop ℤ)<v (-(2*y1*y2)) := by
    rw [v.map_neg,v.map_mul,v.map_mul,h2,hy1,hy2,zero_add]
    exact_mod_cast (show 2*a<b+c by omega)
  let r := x1*x2^2 + -(D*x1) + -(D*x2) + -(2*y1*y2)
  have hrem : ((2*a:ℤ):WithTop ℤ)<v r :=
    v.map_lt_add (v.map_lt_add (v.map_lt_add ht1 ht2) ht3) ht4
  have hnum : v (x1^2*x2+r)=(2*a:ℤ) := by
    rw [v.map_add_eq_of_lt_left]
    · exact hlead
    · rwa [hlead]
  have hid : ((y1-y2)/(x1-x2))^2-x1-x2=(x1^2*x2+r)/(x1-x2)^2 := by
    dsimp [r]
    field_simp [hxx]
    linear_combination hc1+hc2
  rw [hid,v.map_div,hnum,hden]
  norm_cast
  omega

theorem generator_y_value : InertThree318.place yP=(2:ℤ) := by
  rw [InertThree318.place_norm yP yP_ne,LocalGenerator318.norm_yP]
  have hv : padicValRat 3 (43911/512:ℚ)=2 := by
    convert AnchorNorm318.rational_scaled_value 3 2 4879 512 (by norm_num) (by norm_num) using 1 <;> norm_num
  rw [hv]

theorem add_generator_unit (R : E.Point) (a : ℤ) (hR : Depth R a) (ha : a<0) :
    Depth (R+P) 0 := by
  obtain ⟨x,y,h,hpt,hx⟩ := hR
  obtain ⟨_,b,hy,_⟩ := ThreeGroupSteps318.ordinate x y h a hx ha
  have hne : x≠xP := by
    intro he
    have hv := congrArg InertThree318.place he
    rw [hx,InertThree318.generator_x_value] at hv
    have hv' : a=0 := by exact_mod_cast hv
    omega
  have hc1 : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
  have hc2 : yP^2=xP^3-D*xP := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using equationP
  refine ⟨_,_,nonsingular_add h nonsingularP (fun hz => hne hz.1),?_,?_⟩
  · rw [hpt,P]
    exact Point.add_of_X_ne hne
  · rw [addX,slope_of_X_ne hne]
    simp only [E,zero_mul,add_zero,sub_zero]
    exact unit_add_value x y xP yP a b 2 hx hy InertThree318.generator_x_value generator_y_value
      (by norm_num) hc1 hc2 ha

theorem odd_multiple (n : ℤ) (hn : Odd n) : Depth (n • P) 0 := by
  by_cases h1 : n=1
  · subst n
    refine ⟨xP,yP,nonsingularP,?_,InertThree318.generator_x_value⟩
    simp [P]
  have heven : Even (n-1) := by
    obtain ⟨j,hj⟩ := hn
    exact ⟨j,by omega⟩
  have hD := GeneratorMultiplesThree318.even_multiple (n-1) (by omega) heven
  have hA := add_generator_unit _ _ hD (by omega)
  have heq : n • P=(n-1) • P+P := by
    rw [sub_zsmul,one_zsmul]
    abel
  rwa [←heq] at hA

theorem identified_odd_multiple_norm (n : ℤ) (hn : Odd n)
    (x y : K) (h : E.Nonsingular x y) (hpt : n • P=Point.some x y h) :
    padicValRat 3 (AnchorNorm318.norm x)=0 := by
  obtain ⟨x',y',h',hpt',hv⟩ := odd_multiple n hn
  have he : Point.some x' y' h'=Point.some x y h := hpt'.symm.trans hpt
  cases he
  have hx : x≠0 := (InertThree318.place.ne_top_iff).mp (by rw [hv]; simp)
  rw [InertThree318.place_norm _ hx] at hv
  exact_mod_cast hv

end OddMultiplesThree318
