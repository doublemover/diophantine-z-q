module
public import RootPointAlgebra318
public section
namespace KummerGroup318
open ConcreteG8Domain LocalGenerator318 KummerAlgebra318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The signed root formula is attached to actual elliptic subtraction. -/
theorem difference_point (h j : K) (hj : j^2=h^4-D) (hd : h^2≠xP) :
    ∃ (y : K) (hr : E.Nonsingular (((jP*h+hP*j)/(h^2-xP))^2) y),
      Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj)-P=
        Point.some _ y hr := by
  let hs := RootPointAlgebra318.square_point h j hj
  let hp := (nonsingular_neg xP yP).mpr nonsingularP
  let m := E.slope (h^2) xP (h*j) (E.negY xP yP)
  let xx := E.addX (h^2) xP m
  let yy := E.addY (h^2) xP (h*j) m
  have hr : E.Nonsingular xx yy := nonsingular_add hs hp (fun hh => hd hh.1)
  have hadd : Point.some (h^2) (h*j) hs-P=Point.some xx yy hr := by
    rw [sub_eq_add_neg,P,Point.neg_some]
    exact Point.add_of_X_ne hd
  have hxx : xx=((jP*h+hP*j)/(h^2-xP))^2 := by
    change E.addX (h^2) xP (E.slope (h^2) xP (h*j) (E.negY xP yP))=_
    rw [addX,slope_of_X_ne hd]
    simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
    rw [←hP_jP]
    field_simp [sub_ne_zero.mpr hd]
    have hpp := hP_square
    have hjp := jP_square
    linear_combination (h^2-xP)*hj-(h^2-xP)*hjp+(jP^2-j^2)*hpp
  simp only [hxx] at hr hadd
  exact ⟨yy,hr,hadd⟩

/-- The two unequal-abscissa scalar branches give precisely the signed
indices a−1 and −a−1, with the ordinate chosen by actual group subtraction. -/
theorem unequal_orientation (a : ℤ) (h j r : K) (hj : j^2=h^4-D)
    (hlabel : a • P=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj))
    (hd : h^2≠xP)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    ∃(c:ℤ)(y:K)(hr:E.Nonsingular (r^2) y),
      c • P=Point.some _ y hr ∧ (c=a-1 ∨ c= -a-1) := by
  rcases kummer_branches h j r hj hk with hp | hm
  · have he : r=(jP*h+hP*j)/(h^2-xP) :=
      (eq_div_iff (sub_ne_zero.mpr hd)).mpr (by simpa [mul_comm] using hp)
    obtain ⟨y,hr,hpt⟩ := difference_point h j hj hd
    simp only [←he] at hr hpt
    refine ⟨a-1,y,hr,?_,Or.inl rfl⟩
    rw [sub_zsmul,one_zsmul,hlabel]
    exact hpt
  · have hj' : (-j)^2=h^4-D := by simpa using hj
    have he : r=(jP*h+hP*(-j))/(h^2-xP) :=
      (eq_div_iff (sub_ne_zero.mpr hd)).mpr (by linear_combination hm)
    obtain ⟨y,hr,hpt⟩ := difference_point h (-j) hj' hd
    simp only [←he] at hr hpt
    refine ⟨-a-1,y,hr,?_,Or.inr rfl⟩
    rw [sub_zsmul,one_zsmul,neg_zsmul,hlabel,Point.neg_some]
    have hy : E.negY (h^2) (h*j)=h*(-j) := by simp [negY,E]
    simpa only [hy,sub_eq_add_neg] using hpt

theorem label_one_or_neg_one (a : ℤ) (h j : K) (hj : j^2=h^4-D)
    (hlabel : a • P=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj))
    (heq : h^2=xP) : a=1 ∨ a= -1 := by
  have he := (Point.X_eq_iff (h₁:=RootPointAlgebra318.square_point h j hj)
    (h₂:=nonsingularP)).mp heq
  change Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj)=P ∨
    Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj)= -P at he
  rcases he with he | he
  · left
    have hz : (a-1) • P=0 := by rw [sub_zsmul,one_zsmul,hlabel,he,add_neg_cancel]
    by_contra hh
    exact GeneratorMultiplesTwo318.generator_infinite_order (a-1) (by omega) hz
  · right
    have hz : (a+1) • P=0 := by rw [add_zsmul,one_zsmul,hlabel,he,neg_add_cancel]
    by_contra hh
    exact GeneratorMultiplesTwo318.generator_infinite_order (a+1) (by omega) hz

theorem equal_scalar_square (h r : K) (hh : h^2=xP)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) : r^2=x2P := by
  have hmul := kummer_equal_square h r hh hk
  have he : (2*h*jP*r)^2=(2*yP)^2*r^2 := by
    rw [←hP_jP]
    linear_combination 4*jP^2*r^2*(hh-hP_square)
  rw [he] at hmul
  have hdX : E.addX xP xP (E.slope xP xP yP yP)=x2P := by
    rw [addX,slopeP_actual]
    simp only [E,zero_mul,add_zero,sub_zero]
    rw [double_x_identity]
    ring
  have hformula := ValuationDuplication318.actual_doubling_x xP yP nonsingularP yP_ne
  rw [hdX] at hformula
  have htwo : (2*yP)≠0 := mul_ne_zero (by norm_num) yP_ne
  apply (mul_left_cancel₀ (pow_ne_zero 2 htwo))
  rw [hmul,hformula]
  field_simp [htwo,yP_ne]

theorem equal_orientation (a : ℤ) (h j r : K) (hj : j^2=h^4-D)
    (hlabel : a • P=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj))
    (heq : h^2=xP)
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    ∃(c:ℤ)(y:K)(hr:E.Nonsingular (r^2) y),
      c • P=Point.some _ y hr ∧ (c=a-1 ∨ c= -a-1) := by
  have hr := equal_scalar_square h r heq hk
  have ha := label_one_or_neg_one a h j hj hlabel heq
  obtain ⟨hp,hpoint⟩ := actual_double_coordinates
  have hneg : (-2:ℤ) • P=Point.some x2P (E.negY x2P y2P) ((nonsingular_neg x2P y2P).mpr hp) := by
    rw [neg_zsmul,two_zsmul,hpoint,Point.neg_some]
  have hns := (nonsingular_neg x2P y2P).mpr hp
  simp only [←hr] at hns hneg
  refine ⟨-2,_,hns,hneg,?_⟩
  rcases ha with ha | ha
  · right; omega
  · left; omega

/-- Complete signed Kummer orientation, retaining the coincident-abscissa
branch rather than assuming a denominator inverse that the source lacks. -/
theorem scalar_orientation (a : ℤ) (h j r : K) (hj : j^2=h^4-D)
    (hlabel : a • P=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj))
    (hk : (h*r)^2-xP*r^2-2*jP*h*r-xP*h^2-D=0) :
    ∃(c:ℤ)(y:K)(hr:E.Nonsingular (r^2) y),
      c • P=Point.some _ y hr ∧ (c=a-1 ∨ c= -a-1) := by
  by_cases heq : h^2=xP
  · exact equal_orientation a h j r hj hlabel heq hk
  · exact unequal_orientation a h j r hj hlabel heq hk

end KummerGroup318
