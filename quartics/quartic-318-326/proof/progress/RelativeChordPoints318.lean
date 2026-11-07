module
public import RelativeChordScheme318
public import LiteralWeierstrassPoints318
public section
noncomputable section
namespace RelativeChordPoints318
open AffineEquationFunctor318 AffineSchemeSolutions318 LiteralWeierstrassPoints318
open RelativeChordAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]


/-- The actual finite source-model point of an actual coordinate-algebra map. -/
@[expose] def pointOfHom (f:ShortAffineJacobian318.Ring (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[(OpenJModel318.Base N)] K) : (model (K:=K) N).Point :=
  (solutionPoint (model N)
    ⟨(ofHom (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f).val,(solution_iff_equation N _ _).mp (ofHom (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f).property⟩).val

/-- These are exactly the points of the previously bound actual affine Scheme morphisms. -/
theorem pointOfHom_scheme (f:ShortAffineJacobian318.Ring (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[(OpenJModel318.Base N)] K) :
    pointOfHom N f =
      (fieldPointEquiv N ((schemeSolutionEquiv (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).symm (ofHom (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) f))).val := by
  rw [fieldPointEquiv_coordinates]
  rfl

variable (φ:ChordRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) →ₐ[(OpenJModel318.Base N)] K)

theorem coordinates_distinct : φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ≠ φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) := by
  have hh := (gap_unit (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).map φ
  rw [isUnit_iff_ne_zero,map_sub] at hh
  exact fun h => hh (sub_eq_zero.mpr h.symm)

theorem actual_slope [DecidableEq K] : φ (slope (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))=
    (model N).slope (φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (coordinates_distinct N φ)]
  rw [eq_div_iff (sub_ne_zero.mpr (coordinates_distinct N φ))]
  have hh := congrArg φ (slope_identity (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
  simp only [map_mul,map_sub] at hh
  linear_combination -hh

/-- The actual relative Scheme chord morphism agrees with Mathlib's genuine point group law
on every field-valued point of its actual localized fiber-product domain. -/
theorem chord_add [DecidableEq K] :
    pointOfHom N (φ.comp (chordMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) =
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
  simp only [ofHom,AlgHom.comp_apply,chordMap_x,chordMap_y]
  change WeierstrassCurve.Affine.Point.some (φ (x3 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y3 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) _ =
    WeierstrassCurve.Affine.Point.some (φ (x1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y1 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) _ +
    WeierstrassCurve.Affine.Point.some (φ (x2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) (φ (y2 (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (coordinates_distinct N φ),
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [x3,map_sub,map_pow,actual_slope,WeierstrassCurve.Affine.addX,
      ha1,ha2,zero_mul,add_zero,sub_zero]
  · simp only [y3,x3,map_sub,map_mul,map_pow,actual_slope,
      WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.addX,
      ha1,ha2,ha3,zero_mul,add_zero,sub_zero]
    ring

end RelativeChordPoints318
