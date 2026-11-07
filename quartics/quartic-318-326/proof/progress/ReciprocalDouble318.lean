module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic
public section
namespace ReciprocalDouble318
open WeierstrassCurve.Affine
variable {F:Type*} [Field F] [CharZero F]
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
local instance : DecidableEq F := Classical.decEq F

@[expose] def E (D:F) : WeierstrassCurve.Affine F := ⟨0,0,0,-D,0⟩
@[expose] def uDouble (D u v:F) : F := 2*u*v/(1+D*u^4)
@[expose] def vDouble (D u:F) : F := (1-6*D*u^4+D^2*u^8)/(1+D*u^4)^2
@[expose] def tangent (D u v:F) : F := (3-D*u^4)/(2*u*v)

theorem reciprocal_nonsingular (D u v:F) (hu:u≠0) (hv:v≠0)
    (hc:v^2=1-D*u^4) : (E D).Nonsingular (1/u^2) (v/u^3) := by
  rw [nonsingular_iff']
  constructor
  · rw [equation_iff]
    simp only [E,zero_mul,mul_zero,add_zero]
    field_simp [hu]
    linear_combination hc
  · right
    simp only [E,zero_mul,add_zero]
    exact mul_ne_zero (by norm_num) (div_ne_zero hv (pow_ne_zero 3 hu))

theorem doubled_parameter_ne (D u v:F) (hu:u≠0) (hv:v≠0) (hq:1+D*u^4≠0) :
    uDouble D u v≠0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hu) hv) hq

theorem double_x_polynomial (D u v:F) (hc:v^2=1-D*u^4) :
    (3-D*u^4)^2-8*v^2=(1+D*u^4)^2 := by
  linear_combination -8*hc

theorem double_y_polynomial (D u v:F) (hc:v^2=1-D*u^4) :
    (3-D*u^4)*(4*v^2-(1+D*u^4)^2)-8*v^4=
      (1-6*D*u^4+D^2*u^8)*(1+D*u^4) := by
  linear_combination 4*(D*u^4-2*v^2+1)*hc

theorem double_curve (D u v:F) (hq:1+D*u^4≠0) (hc:v^2=1-D*u^4) :
    (vDouble D u)^2=1-D*(uDouble D u v)^4 := by
  dsimp [vDouble,uDouble]
  field_simp [hq]
  linear_combination 16*D*u^4*(v^2+1-D*u^4)*hc

theorem tangent_actual (D u v:F) (hu:u≠0) (hv:v≠0) :
    (E D).slope (1/u^2) (1/u^2) (v/u^3) (v/u^3)=tangent D u v := by
  have hy : v/u^3≠(E D).negY (1/u^2) (v/u^3) := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    exact (mul_ne_zero (show (2:F)≠0 by norm_num) (div_ne_zero hv (pow_ne_zero 3 hu)))
      (by linear_combination hh)
  rw [slope_of_Y_ne' hy]
  simp only [E,zero_mul,mul_zero,add_zero,sub_zero,sub_neg_eq_add]
  dsimp [tangent]
  field_simp [hu,hv]
  ring

theorem double_x (D u v:F) (hu:u≠0) (hv:v≠0) (hq:1+D*u^4≠0)
    (hc:v^2=1-D*u^4) :
    (tangent D u v)^2-1/u^2-1/u^2=1/(uDouble D u v)^2 := by
  dsimp [tangent,uDouble]
  field_simp [hu,hv,hq]
  linear_combination double_x_polynomial D u v hc

theorem double_y (D u v:F) (hu:u≠0) (hv:v≠0) (hq:1+D*u^4≠0)
    (hc:v^2=1-D*u^4) :
    tangent D u v*(1/u^2-1/(uDouble D u v)^2)-v/u^3=
      vDouble D u/(uDouble D u v)^3 := by
  dsimp [tangent,uDouble,vDouble]
  field_simp [hu,hv,hq]
  linear_combination double_y_polynomial D u v hc

/-- Actual Mathlib doubling, not just the rational-coordinate substitution.
The new ordinate may vanish in this general statement. -/
theorem actual_double (D u v:F) (hu:u≠0) (hv:v≠0) (hq:1+D*u^4≠0)
    (hc:v^2=1-D*u^4) :
    ∃h:(E D).Nonsingular (1/(uDouble D u v)^2) (vDouble D u/(uDouble D u v)^3),
      Point.some (1/u^2) (v/u^3) (reciprocal_nonsingular D u v hu hv hc)+
        Point.some (1/u^2) (v/u^3) (reciprocal_nonsingular D u v hu hv hc)=
      Point.some _ _ h := by
  have hy : v/u^3≠(E D).negY (1/u^2) (v/u^3) := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    exact (mul_ne_zero (show (2:F)≠0 by norm_num) (div_ne_zero hv (pow_ne_zero 3 hu)))
      (by linear_combination hh)
  have hx : (E D).addX (1/u^2) (1/u^2) ((E D).slope (1/u^2) (1/u^2) (v/u^3) (v/u^3))=
      1/(uDouble D u v)^2 := by
    rw [tangent_actual D u v hu hv]
    simpa [addX,E] using double_x D u v hu hv hq hc
  have hy' : (E D).addY (1/u^2) (1/u^2) (v/u^3) ((E D).slope (1/u^2) (1/u^2) (v/u^3) (v/u^3))=
      vDouble D u/(uDouble D u v)^3 := by
    rw [addY,negAddY,negY,hx,tangent_actual D u v hu hv]
    simp only [E,zero_mul,sub_zero]
    linear_combination double_y D u v hu hv hq hc
  have hn := nonsingular_add (reciprocal_nonsingular D u v hu hv hc)
    (reciprocal_nonsingular D u v hu hv hc) (fun h => hy h.2)
  rw [hx,hy'] at hn
  refine ⟨hn,?_⟩
  rw [Point.add_self_of_Y_ne hy]
  simp only [hx,hy']

@[expose] def point (D u v:F) (hv:v≠0) (hc:v^2=1-D*u^4) : (E D).Point :=
  if hu:u=0 then 0 else Point.some (1/u^2) (v/u^3) (reciprocal_nonsingular D u v hu hv hc)

theorem point_zero (D v:F) (hv:v≠0) (hc:v^2=1-D*(0:F)^4) : point D 0 v hv hc=0 := by
  simp [point]

theorem point_negative (D u v:F) (hv:v≠0) (hc:v^2=1-D*u^4) :
    point D (-u) v hv (by convert hc using 1 <;> ring)= -point D u v hv hc := by
  by_cases hu:u=0
  · simp [point,hu]
  · simp only [point,dite_eq_right hu,dite_eq_right (neg_ne_zero.mpr hu),Point.neg_some]
    simp [negY,E]
    rw [show (-u)^3= -(u^3) by ring,div_neg]

theorem point_add_inverse (D u v:F) (hv:v≠0) (hc:v^2=1-D*u^4) :
    point D u v hv hc+point D (-u) v hv (by convert hc using 1 <;> ring)=0 := by
  rw [point_negative D u v hv hc,add_neg_cancel]

/-- Zero-aware doubling in the actual elliptic group. The output ordinate
nonvanishing is automatic on the positive local branch, and stated explicitly here. -/
theorem point_double (D u v:F) (hv:v≠0) (hc:v^2=1-D*u^4)
    (hq:1+D*u^4≠0) (hvd:vDouble D u≠0) :
    point D u v hv hc+point D u v hv hc=
      point D (uDouble D u v) (vDouble D u) hvd (double_curve D u v hq hc) := by
  by_cases hu:u=0
  · subst u
    simp [point,uDouble,vDouble]
  · obtain ⟨h,he⟩ := actual_double D u v hu hv hq hc
    simpa only [point,dite_eq_right hu,
      dite_eq_right (doubled_parameter_ne D u v hu hv hq)] using he

/-- Both identity charts are actual group identities, including the zero input. -/
theorem point_add_identity (D u v:F) (hv:v≠0) (hc:v^2=1-D*u^4) :
    point D u v hv hc+point D 0 1 (by norm_num) (by ring)=point D u v hv hc := by
  rw [point_zero,add_zero]

end
end ReciprocalDouble318
#print axioms ReciprocalDouble318.actual_double
#print axioms ReciprocalDouble318.point_double
#print axioms ReciprocalDouble318.point_add_inverse
