module
public import TangentOpenScheme318
public import RelativeChordPoints318
public import LiteralWeierstrassPoints318
public section
noncomputable section
namespace TangentOpenPoints318
open AffineEquationFunctor318 AffineSchemeSolutions318 LiteralWeierstrassPoints318
open TangentOpenAlgebra318
open RelativeChordPoints318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]


variable (φ:TangentRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[(OpenJModel318.Base N)] K)

theorem ordinate_nonzero : (φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))+(φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) ≠ 0 := by
  have hh := (sum_unit (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).map φ
  simpa only [isUnit_iff_ne_zero,map_add] using hh

theorem nonvertical : (φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) ≠ (model N).negY (φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
  have ha1 : (model (K:=K) N).a₁=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  have ha3 : (model (K:=K) N).a₃=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  simp only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero]
  intro h
  exact ordinate_nonzero N φ (by rw [h]; ring)

theorem actual_slope [DecidableEq K] : (φ (slope (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))=
    (model N).slope (φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
  by_cases hx : (φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))=(φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))
  · have ha1 : (model (K:=K) N).a₁=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
    have ha2 : (model (K:=K) N).a₂=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
    have ha3 : (model (K:=K) N).a₃=0 := by
      simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
        OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
    have ha4 : (model (K:=K) N).a₄=algebraMap (OpenJModel318.Base N) K (OpenJAffineScheme318.A N) := rfl
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hx (nonvertical N φ)]
    simp only [ha1,ha2,ha4,WeierstrassCurve.Affine.negY,ha3,zero_mul,mul_zero,
      add_zero,sub_zero,sub_neg_eq_add]
    have hy : φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))=
        φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) := by
      have hh:=congrArg φ (slope_gap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
      simp only [map_mul,map_sub,←hx,sub_self,mul_zero] at hh
      exact sub_eq_zero.mp hh.symm
    have hsum : φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))+
        φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ≠ 0 := by
      simpa only [hy] using ordinate_nonzero N φ
    rw [eq_div_iff hsum]
    have hh := congrArg φ (slope_sum (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    simp only [map_mul,map_add,map_pow,AlgHom.commutes] at hh
    rw [←hx,hy] at hh
    linear_combination hh
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx,eq_div_iff (sub_ne_zero.mpr hx)]
    have hh := congrArg φ (slope_gap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    simp only [map_mul,map_sub] at hh
    linear_combination -hh

/-- The actual relative Scheme chord morphism agrees with Mathlib's genuine point group law
on every field-valued point of its actual localized fiber-product domain. -/
theorem tangent_add [DecidableEq K] :
    pointOfHom N (φ.comp (tangentMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) =
      pointOfHom N (φ.comp (left (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) + pointOfHom N (φ.comp (right (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
  have ha1 : (model (K:=K) N).a₁=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  have ha2 : (model (K:=K) N).a₂=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  have ha3 : (model (K:=K) N).a₃=0 := by
    simp only [model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      OpenJModel318.integralModel,OpenJModel318.curve,map_zero]
  unfold pointOfHom solutionPoint
  simp only [ofHom,AlgHom.comp_apply,tangentMap_x,tangentMap_y]
  change WeierstrassCurve.Affine.Point.some (φ (x3 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y3 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) _ =
    WeierstrassCurve.Affine.Point.some ((φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))) ((φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))) _ +
    WeierstrassCurve.Affine.Point.some ((φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))) ((φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)))) _
  rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (nonvertical N φ),
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [x3,map_sub,map_pow,actual_slope,WeierstrassCurve.Affine.addX,
      ha1,ha2,zero_mul,add_zero,sub_zero]
  · simp only [y3,x3,map_sub,map_mul,map_pow,actual_slope,
      WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.addX,
      ha1,ha2,ha3,zero_mul,add_zero,sub_zero]
    ring

end TangentOpenPoints318
