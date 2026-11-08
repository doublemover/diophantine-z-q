module
public import RelativeChordScheme318
public import RationalWeierstrassPoints318
public section
noncomputable section
namespace RationalChordPoints318
open AffineEquationFunctor318 AffineSchemeSolutions318 RationalWeierstrassPoints318
open RelativeChordAlgebra318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
variable {K:Type} [Field K] [Algebra ℚ K]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD


/-- The actual finite source-model point of an actual coordinate-algebra map. -/
@[expose] def pointOfHom (f:ShortAffineJacobian318.Ring A B →ₐ[ℚ] K) : (model (K:=K) A B hD).Point :=
  (solutionPoint (model A B hD)
    ⟨(ofHom A B f).val,(solution_iff_equation A B hD _ _).mp (ofHom A B f).property⟩).val

/-- These are exactly the points of the previously bound actual affine Scheme morphisms. -/
theorem pointOfHom_scheme (f:ShortAffineJacobian318.Ring A B →ₐ[ℚ] K) :
    pointOfHom A B hD f =
      (fieldPointEquiv A B hD ((schemeSolutionEquiv A B).symm (ofHom A B f))).val := by
  rw [fieldPointEquiv_coordinates]
  rfl

variable (φ:ChordRing A B →ₐ[ℚ] K)

theorem coordinates_distinct : φ (x1 A B) ≠ φ (x2 A B) := by
  have hh := (gap_unit A B).map φ
  rw [isUnit_iff_ne_zero,map_sub] at hh
  exact fun h => hh (sub_eq_zero.mpr h.symm)

theorem actual_slope [DecidableEq K] : φ (slope A B)=
    (model A B hD).slope (φ (x1 A B)) (φ (x2 A B)) (φ (y1 A B)) (φ (y2 A B)) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (coordinates_distinct A B hD φ)]
  rw [eq_div_iff (sub_ne_zero.mpr (coordinates_distinct A B hD φ))]
  have hh := congrArg φ (slope_identity A B)
  simp only [map_mul,map_sub] at hh
  linear_combination -hh

/-- The actual relative Scheme chord morphism agrees with Mathlib's genuine point group law
on every field-valued point of its actual localized fiber-product domain. -/
theorem chord_add [DecidableEq K] :
    pointOfHom A B hD (φ.comp (chordMap A B)) =
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
  simp only [ofHom,AlgHom.comp_apply,chordMap_x,chordMap_y]
  change WeierstrassCurve.Affine.Point.some (φ (x3 A B)) (φ (y3 A B)) _ =
    WeierstrassCurve.Affine.Point.some (φ (x1 A B)) (φ (y1 A B)) _ +
    WeierstrassCurve.Affine.Point.some (φ (x2 A B)) (φ (y2 A B)) _
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (coordinates_distinct A B hD φ),
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [x3,map_sub,map_pow,actual_slope A B hD φ,WeierstrassCurve.Affine.addX,
      ha1,ha2,zero_mul,add_zero,sub_zero]
  · simp only [y3,x3,map_sub,map_mul,map_pow,actual_slope A B hD φ,
      WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.addX,
      ha1,ha2,ha3,zero_mul,add_zero,sub_zero]
    ring

end RationalChordPoints318
