module
public import TangentOpenScheme318
public import RationalChordPoints318
public import RationalWeierstrassPoints318
public section
noncomputable section
namespace RationalTangentPoints318
open AffineEquationFunctor318 AffineSchemeSolutions318 RationalWeierstrassPoints318
open TangentOpenAlgebra318
open RationalChordPoints318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable {K:Type} [Field K] [Algebra ℚ K]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD


variable (φ:TangentRing A B →ₐ[ℚ] K)

theorem ordinate_nonzero : (φ (y1 A B))+(φ (y2 A B)) ≠ 0 := by
  have hh := (sum_unit A B).map φ
  simpa only [isUnit_iff_ne_zero,map_add] using hh

theorem nonvertical : (φ (y1 A B)) ≠ (model A B hD).negY (φ (x2 A B)) (φ (y2 A B)) := by
  have ha1 : (model (K:=K) A B hD).a₁=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  have ha3 : (model (K:=K) A B hD).a₃=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  simp only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero]
  intro h
  exact ordinate_nonzero A B hD φ (by rw [h]; ring)

theorem actual_slope [DecidableEq K] : (φ (slope A B))=
    (model A B hD).slope (φ (x1 A B)) (φ (x2 A B)) (φ (y1 A B)) (φ (y2 A B)) := by
  by_cases hx : (φ (x1 A B))=(φ (x2 A B))
  · have ha1 : (model (K:=K) A B hD).a₁=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        map_zero]
    have ha2 : (model (K:=K) A B hD).a₂=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        map_zero]
    have ha3 : (model (K:=K) A B hD).a₃=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        map_zero]
    have ha4 : (model (K:=K) A B hD).a₄=algebraMap ℚ K A := rfl
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hx (nonvertical A B hD φ)]
    simp only [ha1,ha2,ha4,WeierstrassCurve.Affine.negY,ha3,zero_mul,mul_zero,
      add_zero,sub_zero,sub_neg_eq_add]
    have hy : φ (y2 A B)=
        φ (y1 A B) := by
      have hh:=congrArg φ (slope_gap A B)
      simp only [map_mul,map_sub,←hx,sub_self,mul_zero] at hh
      exact sub_eq_zero.mp hh.symm
    have hsum : φ (y1 A B)+
        φ (y1 A B) ≠ 0 := by
      simpa only [hy] using ordinate_nonzero A B hD φ
    rw [eq_div_iff hsum]
    have hh := congrArg φ (slope_sum A B)
    simp only [map_mul,map_add,map_pow,AlgHom.commutes] at hh
    rw [←hx,hy] at hh
    linear_combination hh
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx,eq_div_iff (sub_ne_zero.mpr hx)]
    have hh := congrArg φ (slope_gap A B)
    simp only [map_mul,map_sub] at hh
    linear_combination -hh

/-- The actual relative Scheme chord morphism agrees with Mathlib's genuine point group law
on every field-valued point of its actual localized fiber-product domain. -/
theorem tangent_add [DecidableEq K] :
    pointOfHom A B hD (φ.comp (tangentMap A B)) =
      pointOfHom A B hD (φ.comp (left A B)) + pointOfHom A B hD (φ.comp (right A B)) := by
  have ha1 : (model (K:=K) A B hD).a₁=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  have ha2 : (model (K:=K) A B hD).a₂=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  have ha3 : (model (K:=K) A B hD).a₃=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  unfold pointOfHom solutionPoint
  simp only [ofHom,AlgHom.comp_apply,tangentMap_x,tangentMap_y]
  change WeierstrassCurve.Affine.Point.some (φ (x3 A B)) (φ (y3 A B)) _ =
    WeierstrassCurve.Affine.Point.some ((φ (x1 A B))) ((φ (y1 A B))) _ +
    WeierstrassCurve.Affine.Point.some ((φ (x2 A B))) ((φ (y2 A B))) _
  rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (nonvertical A B hD φ),
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [x3,map_sub,map_pow,actual_slope A B hD φ,WeierstrassCurve.Affine.addX,
      ha1,ha2,zero_mul,add_zero,sub_zero]
  · simp only [y3,x3,map_sub,map_mul,map_pow,actual_slope A B hD φ,
      WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.addX,
      ha1,ha2,ha3,zero_mul,add_zero,sub_zero]
    ring

end RationalTangentPoints318
