module
public import RamifiedTwo318
public import ValuationCurveParity
public section
namespace ValuationDuplication318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0

/-- Exact doubling depth on y²=x³−Dx at a negative-x place. No formal
logarithm, convergence theorem, or good-reduction hypothesis is used. -/
theorem duplication_value {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D x y : F) (a b e : ℤ) (hD : v D=0) (hx : v x=a) (hy : v y=b)
    (he : v (2:F)=e) (hc : y^2=x^3-D*x) (ha : a<0) :
    v (((x^2+D)/(2*y))^2)=(a-2*e:ℤ) := by
  have hx2 : v (x^2)=(2*a:ℤ) := by rw [v.map_pow,hx]; norm_cast
  have hx3 : v (x^3)=(3*a:ℤ) := by rw [v.map_pow,hx]; norm_cast
  have hDx : v (D*x)=(a:ℤ) := by rw [v.map_mul,hD,hx,zero_add]
  have hcval : v (x^3-D*x)=(3*a:ℤ) := by
    rw [v.map_sub_eq_of_lt_left]
    · exact hx3
    · rw [hx3,hDx]
      exact_mod_cast (show 3*a<a by omega)
  have hy2 := congrArg v hc
  rw [v.map_pow,hy,hcval] at hy2
  have hab : 2*b=3*a := by exact_mod_cast hy2
  have hsum : v (x^2+D)=(2*a:ℤ) := by
    rw [v.map_add_eq_of_lt_left]
    · exact hx2
    · rw [hx2,hD]
      exact_mod_cast (show 2*a<0 by omega)
  have hden : v (2*y)=(e+b:ℤ) := by rw [v.map_mul,he,hy]; norm_cast
  rw [v.map_pow,v.map_div,hsum,hden]
  have hh : 2*(2*a-(e+b))=a-2*e := by omega
  exact_mod_cast hh

/-- The actual affine doubling abscissa agrees with the square formula. -/
theorem actual_doubling_x (x y : K) (h : E.Nonsingular x y) (hy : y≠0) :
    E.addX x x (E.slope x x y y)=((x^2+D)/(2*y))^2 := by
  have hneg : y≠E.negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    have hz : 2*y=0 := by linear_combination hh
    exact (mul_ne_zero (by norm_num) hy) hz
  have hc : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
  have hs : E.slope x x y y=(3*x^2-D)/(2*y) := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
    congr 1 <;> ring
  rw [addX,hs]
  simp only [E,zero_mul,add_zero,sub_zero]
  field_simp [hy]
  linear_combination -8*x*hc

/-- For the newly constructed actual 2-adic place, each doubling of a
nonzero point on the negative-x branch lowers x-valuation by exactly four. -/
theorem actual_two_doubling (x y : K) (h : E.Nonsingular x y)
    (a : ℤ) (hx : RamifiedTwo318.place x=a) (ha : a<0) :
    ∃ h2 : E.Nonsingular
        (E.addX x x (E.slope x x y y)) (E.addY x x y (E.slope x x y y)),
      Point.some x y h+Point.some x y h=
        Point.some _ _ h2 ∧
      RamifiedTwo318.place (E.addX x x (E.slope x x y y))=(a-4:ℤ) := by
  have hc : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
  have hy : y≠0 := by
    intro hz
    have hf : x*(x^2-D)=0 := by rw [hz] at hc; linear_combination -hc
    have hx0 : x≠0 := (RamifiedTwo318.place.ne_top_iff).mp (by rw [hx]; exact WithTop.coe_ne_top)
    have hd : x^2=D := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hx0)
    have hv := congrArg RamifiedTwo318.place hd
    rw [AddValuation.map_pow,hx,RamifiedTwo318.place_D] at hv
    have hv' : 2*a=0 := by exact_mod_cast hv
    omega
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((RamifiedTwo318.place.ne_top_iff).mpr hy)
  have hneg : y≠E.negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    have hz : 2*y=0 := by linear_combination hh
    exact (mul_ne_zero (by norm_num) hy) hz
  refine ⟨nonsingular_add h h (fun hh => hneg hh.2),Point.add_self_of_Y_ne hneg,?_⟩
  rw [actual_doubling_x x y h hy]
  exact duplication_value RamifiedTwo318.place D x y a b 2 RamifiedTwo318.place_D hx
    hb.symm RamifiedTwo318.place_two hc ha

end ValuationDuplication318
