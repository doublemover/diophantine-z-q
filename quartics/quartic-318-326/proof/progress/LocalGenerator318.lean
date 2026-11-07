module
public import AnchorNorm318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
namespace LocalGenerator318
open ConcreteG8Domain AnchorNorm318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The exact normalized curve used by the current source. -/
@[expose] def E : WeierstrassCurve.Affine K := ⟨0,0,0,-D,0⟩
@[expose] def xP : K := pair (57/8) (-7/2)
@[expose] def yP : K := pair (-165/8) (417/32)
@[expose] def zP : K := pair (232/357) (86/357)
@[expose] def slopeP : K := pair (-117241/29274) (111407/117096)
@[expose] def x2P : K := pair (8226963211/2285245536) (-1063929023/1713934152)
@[expose] def y2P : K := pair (206505981889175/200694833462592) (1488119581317589/802779333850368)
@[expose] def z2P : K := pair (3396356159088/3287811625151) (-4135204317756/3287811625151)

theorem equationP : E.Equation xP yP := by
  rw [equation_iff]
  ext <;> norm_num [E,xP,yP,D,i,pair,pow_succ]

theorem yP_ne : yP≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [yP,pair] at hh

theorem nonsingularP : E.Nonsingular xP yP := by
  rw [nonsingular_iff']
  refine ⟨equationP,Or.inr ?_⟩
  simpa [E] using mul_ne_zero (show (2:K)≠0 by norm_num) yP_ne

@[expose] def P : E.Point := .some xP yP nonsingularP

theorem slope_identity : slopeP*(2*yP)=3*xP^2-D := by
  ext <;> norm_num [slopeP,xP,yP,D,i,pair,pow_succ]

theorem double_x_identity : x2P=slopeP^2-2*xP := by
  ext <;> norm_num [x2P,slopeP,xP,pair,pow_succ]

theorem double_y_identity : y2P=slopeP*(xP-x2P)-yP := by
  ext <;> norm_num [y2P,slopeP,xP,x2P,yP,pair,pow_succ]

theorem slopeP_actual : E.slope xP xP yP yP=slopeP := by
  rw [slope_of_Y_ne']
  · simp only [E,zero_mul,add_zero,sub_zero,sub_neg_eq_add]
    apply (div_eq_iff (show yP+yP≠0 by simpa [two_mul] using mul_ne_zero (show (2:K)≠0 by norm_num) yP_ne)).mpr
    simpa [two_mul,sub_eq_add_neg] using slope_identity.symm
  · simp only [E,zero_mul,sub_zero]
    intro h
    have hh : 2*yP=0 := by linear_combination h
    exact (mul_ne_zero (by norm_num) yP_ne) hh

theorem actual_double_coordinates : ∃ h : E.Nonsingular x2P y2P,
    P+P=Point.some x2P y2P h := by
  have hy : yP≠E.negY xP yP := by
    simp only [negY,E,zero_mul,sub_zero]
    intro h
    have hh : 2*yP=0 := by linear_combination h
    exact (mul_ne_zero (by norm_num) yP_ne) hh
  have hx : E.addX xP xP (E.slope xP xP yP yP)=x2P := by
    rw [slopeP_actual,addX]
    simp only [E,mul_zero,zero_mul,add_zero,sub_zero]
    rw [double_x_identity]
    ring
  have hy' : E.addY xP xP yP (E.slope xP xP yP yP)=y2P := by
    rw [addY,negAddY,negY,hx,slopeP_actual]
    simp only [E,zero_mul,sub_zero]
    rw [double_y_identity]
    ring
  have hns := nonsingular_add nonsingularP nonsingularP (fun h => hy h.2)
  rw [hx,hy'] at hns
  refine ⟨hns,?_⟩
  rw [P,Point.add_self_of_Y_ne hy]
  congr

/-- The literal z-coordinates are verified through multiplication, without
silently using a totalized division at a zero ordinate. -/
theorem zP_identity : zP*yP= -xP := by
  ext <;> norm_num [zP,yP,xP,pair]

theorem z2P_identity : z2P*y2P= -x2P := by
  ext <;> norm_num [z2P,y2P,x2P,pair]

theorem y2P_ne : y2P≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [y2P,pair] at hh

theorem zP_eq : zP= -xP/yP := (eq_div_iff yP_ne).mpr zP_identity

theorem z2P_eq : z2P= -x2P/y2P := (eq_div_iff y2P_ne).mpr z2P_identity

theorem norm_xP : norm xP=1681/64 := by norm_num [xP,norm_pair]
theorem norm_yP : norm yP=43911/512 := by norm_num [yP,norm_pair]
theorem norm_zP : norm zP=328/1071 := by norm_num [zP,norm_pair]
theorem norm_z2P : norm z2P= -6893519740128/3287811625151 := by norm_num [z2P,norm_pair]

theorem two_value_xP : padicValRat 2 (norm xP)= -6 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [norm_xP]
  convert rational_scaled_value 2 (-6) 1681 1 (by norm_num) (by norm_num) using 1 <;> norm_num

theorem two_value_yP : padicValRat 2 (norm yP)= -9 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [norm_yP]
  convert rational_scaled_value 2 (-9) 43911 1 (by norm_num) (by norm_num) using 1 <;> norm_num

theorem two_value_zP : padicValRat 2 (norm zP)=3 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [norm_zP]
  convert rational_scaled_value 2 3 41 1071 (by norm_num) (by norm_num) using 1 <;> norm_num

theorem three_value_xP : padicValRat 3 (norm xP)=0 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [norm_xP]
  exact rational_unit_value 3 1681 64 (by norm_num) (by norm_num)

theorem three_value_z2P : padicValRat 3 (norm z2P)=2 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [norm_z2P]
  convert rational_scaled_value 3 2 (-765946637792) 3287811625151 (by norm_num) (by norm_num) using 1 <;> norm_num

end
end LocalGenerator318
