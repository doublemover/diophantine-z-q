module
public import ValuationDuplication318
public section
namespace ValuationAddition318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0

/-- The curve itself fixes the ordinate valuation on the formal branch. -/
theorem ordinate_value {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D x y : F) (a b : ℤ) (hD : v D=0) (hx : v x=a) (hy : v y=b)
    (hc : y^2=x^3-D*x) (ha : a<0) : 2*b=3*a := by
  have hx3 : v (x^3)=(3*a:ℤ) := by rw [v.map_pow,hx]; norm_cast
  have hDx : v (D*x)=(a:ℤ) := by rw [v.map_mul,hD,hx,zero_add]
  have hcval : v (x^3-D*x)=(3*a:ℤ) := by
    rw [v.map_sub_eq_of_lt_left]
    · exact hx3
    · rw [hx3,hDx]
      exact_mod_cast (show 3*a<a by omega)
  have hy2 := congrArg v hc
  rw [v.map_pow,hy,hcval] at hy2
  exact_mod_cast hy2

/-- The cancellation in the usual slope formula is resolved algebraically.
For distinct negative depths the sum has exactly the shallower depth. -/
theorem unequal_add_value {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D x1 y1 x2 y2 : F) (a1 b1 a2 b2 e : ℤ)
    (hD : v D=0) (hx1 : v x1=a1) (hy1 : v y1=b1)
    (hx2 : v x2=a2) (hy2 : v y2=b2) (he : v (2:F)=e) (he0 : 0≤e)
    (hc1 : y1^2=x1^3-D*x1) (hc2 : y2^2=x2^3-D*x2)
    (ha12 : a1<a2) (ha2 : a2<0) :
    v (((y1-y2)/(x1-x2))^2-x1-x2)=(a2:ℤ) := by
  have ha1 : a1<0 := lt_trans ha12 ha2
  have hb1 := ordinate_value v D x1 y1 a1 b1 hD hx1 hy1 hc1 ha1
  have hb2 := ordinate_value v D x2 y2 a2 b2 hD hx2 hy2 hc2 ha2
  have hxx : x1-x2≠0 := by
    intro h
    have hxe := sub_eq_zero.mp h
    have hh := congrArg v hxe
    rw [hx1,hx2] at hh
    have hh' : a1=a2 := by exact_mod_cast hh
    omega
  have hden : v ((x1-x2)^2)=(2*a1:ℤ) := by
    rw [v.map_pow,v.map_sub_eq_of_lt_left]
    · rw [hx1]; norm_cast
    · rw [hx1,hx2]; exact_mod_cast ha12
  have hlead : v (x1^2*x2)=(2*a1+a2:ℤ) := by
    rw [v.map_mul,v.map_pow,hx1,hx2]; norm_cast
  have ht1 : ((2*a1+a2:ℤ):WithTop ℤ)<v (x1*x2^2) := by
    rw [v.map_mul,v.map_pow,hx1,hx2]
    exact_mod_cast (show 2*a1+a2<a1+2*a2 by omega)
  have ht2 : ((2*a1+a2:ℤ):WithTop ℤ)<v (-(D*x1)) := by
    rw [v.map_neg,v.map_mul,hD,hx1,zero_add]
    exact_mod_cast (show 2*a1+a2<a1 by omega)
  have ht3 : ((2*a1+a2:ℤ):WithTop ℤ)<v (-(D*x2)) := by
    rw [v.map_neg,v.map_mul,hD,hx2,zero_add]
    exact_mod_cast (show 2*a1+a2<a2 by omega)
  have ht4 : ((2*a1+a2:ℤ):WithTop ℤ)<v (-(2*y1*y2)) := by
    rw [v.map_neg,v.map_mul,v.map_mul,he,hy1,hy2]
    exact_mod_cast (show 2*a1+a2<e+b1+b2 by omega)
  let r := x1*x2^2 + -(D*x1) + -(D*x2) + -(2*y1*y2)
  have hrem : ((2*a1+a2:ℤ):WithTop ℤ)<v r :=
    v.map_lt_add (v.map_lt_add (v.map_lt_add ht1 ht2) ht3) ht4
  have hnum : v (x1^2*x2+r)=(2*a1+a2:ℤ) := by
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

/-- Every actual point with negative x-valuation has a finite ordinate value. -/
theorem actual_ordinate (x y : K) (h : E.Nonsingular x y)
    (a : ℤ) (hx : RamifiedTwo318.place x=a) (ha : a<0) :
    ∃ b : ℤ,RamifiedTwo318.place y=b ∧ 2*b=3*a := by
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
  exact ⟨b,hb.symm,ordinate_value RamifiedTwo318.place D x y a b RamifiedTwo318.place_D hx hb.symm hc ha⟩

/-- The valuation statement is attached to actual Mathlib point addition. -/
theorem actual_two_unequal_add (x1 y1 x2 y2 : K)
    (h1 : E.Nonsingular x1 y1) (h2 : E.Nonsingular x2 y2)
    (a1 a2 : ℤ) (hx1 : RamifiedTwo318.place x1=a1) (hx2 : RamifiedTwo318.place x2=a2)
    (ha12 : a1<a2) (ha2 : a2<0) :
    ∃ h : E.Nonsingular
        (E.addX x1 x2 (E.slope x1 x2 y1 y2)) (E.addY x1 x2 y1 (E.slope x1 x2 y1 y2)),
      Point.some x1 y1 h1+Point.some x2 y2 h2=Point.some _ _ h ∧
      RamifiedTwo318.place (E.addX x1 x2 (E.slope x1 x2 y1 y2))=(a2:ℤ) := by
  have hne : x1≠x2 := by
    intro hh
    have hv := congrArg RamifiedTwo318.place hh
    rw [hx1,hx2] at hv
    have hv' : a1=a2 := by exact_mod_cast hv
    omega
  obtain ⟨b1,hb1,_⟩ := actual_ordinate x1 y1 h1 a1 hx1 (lt_trans ha12 ha2)
  obtain ⟨b2,hb2,_⟩ := actual_ordinate x2 y2 h2 a2 hx2 ha2
  have hc1 : y1^2=x1^3-D*x1 := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h1.1
  have hc2 : y2^2=x2^3-D*x2 := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h2.1
  refine ⟨nonsingular_add h1 h2 (fun hh => hne hh.1),Point.add_of_X_ne hne,?_⟩
  rw [addX,slope_of_X_ne hne]
  simp only [E,zero_mul,add_zero,sub_zero]
  exact unequal_add_value RamifiedTwo318.place D x1 y1 x2 y2 a1 b1 a2 b2 2
    RamifiedTwo318.place_D hx1 hb1 hx2 hb2 RamifiedTwo318.place_two (by norm_num) hc1 hc2 ha12 ha2

end ValuationAddition318
