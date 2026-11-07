module
public import ValuationTriplication318
public section
namespace ThreeGroupSteps318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def Depth (R : E.Point) (a : ℤ) : Prop :=
  ∃ (x y : K) (h : E.Nonsingular x y), R=Point.some x y h ∧ InertThree318.place x=a

/-- On the formal branch the ordinate is nonzero, with valuation 3a/2. -/
theorem ordinate (x y : K) (h : E.Nonsingular x y)
    (a : ℤ) (hx : InertThree318.place x=a) (ha : a<0) :
    y≠0 ∧ ∃b:ℤ,InertThree318.place y=b ∧ 2*b=3*a := by
  have hc : y^2=x^3-D*x := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
  have hy : y≠0 := by
    intro hz
    have hf : x*(x^2-D)=0 := by rw [hz] at hc; linear_combination -hc
    have hx0 : x≠0 := (InertThree318.place.ne_top_iff).mp (by rw [hx]; exact WithTop.coe_ne_top)
    have hd : x^2=D := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hx0)
    have hv := congrArg InertThree318.place hd
    rw [AddValuation.map_pow,hx,InertThree318.place_D] at hv
    have hv' : 2*a=0 := by exact_mod_cast hv
    omega
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((InertThree318.place.ne_top_iff).mpr hy)
  exact ⟨hy,b,hb.symm,ValuationAddition318.ordinate_value InertThree318.place D x y a b
    InertThree318.place_D hx hb.symm hc ha⟩

theorem triple_depth (R : E.Point) (a : ℤ) (hR : Depth R a) (ha : a≤ -4) :
    Depth ((3:ℕ) • R) (a-4) := by
  obtain ⟨x,y,h,hpt,hx⟩ := hR
  have hy := (ordinate x y h a hx (by omega)).1
  have hp : ValuationTriplication318.psi x≠0 := by
    apply (InertThree318.place.ne_top_iff).mp
    rw [(ValuationTriplication318.polynomial_values x a hx ha).1]
    exact WithTop.coe_ne_top
  obtain ⟨xx,yy,hh,hsum,hxx⟩ := ValuationTriplication318.actual_tripling_x x y h hy hp
  refine ⟨xx,yy,hh,?_,?_⟩
  · rw [hpt,show (3:ℕ)=2+1 by rfl,add_nsmul,two_nsmul,one_nsmul]
    exact hsum
  · rw [hxx]
    exact ValuationTriplication318.triplication_value x a hx ha

theorem add_depth (R S : E.Point) (a b : ℤ) (hR : Depth R a) (hS : Depth S b)
    (hab : a<b) (hb : b<0) : Depth (R+S) b := by
  obtain ⟨x1,y1,h1,hpt1,hx1⟩ := hR
  obtain ⟨x2,y2,h2,hpt2,hx2⟩ := hS
  have hne : x1≠x2 := by
    intro hh
    have hv := congrArg InertThree318.place hh
    rw [hx1,hx2] at hv
    have hv' : a=b := by exact_mod_cast hv
    omega
  obtain ⟨_,b1,hb1,_⟩ := ordinate x1 y1 h1 a hx1 (lt_trans hab hb)
  obtain ⟨_,b2,hb2,_⟩ := ordinate x2 y2 h2 b hx2 hb
  have hc1 : y1^2=x1^3-D*x1 := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h1.1
  have hc2 : y2^2=x2^3-D*x2 := by
    simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h2.1
  refine ⟨_,_,nonsingular_add h1 h2 (fun hh => hne hh.1),?_,?_⟩
  · rw [hpt1,hpt2]
    exact Point.add_of_X_ne hne
  · rw [addX,slope_of_X_ne hne]
    simp only [E,zero_mul,add_zero,sub_zero]
    exact ValuationAddition318.unequal_add_value InertThree318.place D x1 y1 x2 y2 a b1 b b2 0
      InertThree318.place_D hx1 hb1 hx2 hb2 InertThree318.place_two (by norm_num) hc1 hc2 hab hb

theorem neg_depth (R : E.Point) (a : ℤ) (hR : Depth R a) : Depth (-R) a := by
  obtain ⟨x,y,h,hpt,hx⟩ := hR
  refine ⟨x,E.negY x y,(nonsingular_neg x y).mpr h,?_,hx⟩
  rw [hpt]
  rfl

@[expose] noncomputable def Q : E.Point := P+P

theorem base_depth : Depth Q (-4) := by
  obtain ⟨h,hpt⟩ := LocalGenerator318.actual_double_coordinates
  exact ⟨x2P,y2P,h,hpt,InertThree318.doubled_generator_x_value⟩

end ThreeGroupSteps318
