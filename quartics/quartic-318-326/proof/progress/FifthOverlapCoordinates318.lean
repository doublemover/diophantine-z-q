module
public import FifthSourceOverlap318
public import FifthQuarticFiniteCoordinates318
public import FifthGlobalIndependence318
public section
noncomputable section
namespace FifthOverlapCoordinates318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev O:=ContactKummerOrder318.OpenOrder units
@[expose] def t:O:=SourceInfinityOverlap318.t units
@[expose] def w:O:=FifthSourceOverlap318.input
  (AdjoinRoot.root (QuadraticPresentation318.polynomial FifthCharacterPolynomial318.quartic))
@[expose] def x:O:=FifthSourceOverlap318.shortMap (ShortAffineJacobian318.x A B)
@[expose] def y:O:=FifthSourceOverlap318.shortMap (ShortAffineJacobian318.y A B)
lemma lift_t:FifthSourceOverlap318.lift FifthQuarticFiniteCoordinates318.t=t:=by
  rw [FifthQuarticFiniteCoordinates318.t,FifthSourceOverlap318.lift_on_order,
    FifthSourceOverlap318.input_parameter]
  rfl
lemma lift_w:FifthSourceOverlap318.lift FifthQuarticFiniteCoordinates318.w=w:=
  FifthSourceOverlap318.lift_on_order _
theorem x_relation:x*t=algebraMap ℚ O (xScale:ℚ)+algebraMap ℚ O shift*t:=by
  have h:=congrArg FifthSourceOverlap318.lift FifthQuarticFiniteCoordinates318.x_relation
  simpa only [map_mul,map_add,AlgHom.commutes,lift_t,x,FifthSourceOverlap318.shortMap,AlgHom.comp_apply] using h
theorem y_relation:y*t^2=algebraMap ℚ O (yScale:ℚ)*w:=by
  have h:=congrArg FifthSourceOverlap318.lift FifthQuarticFiniteCoordinates318.y_relation
  simpa only [map_mul,map_pow,AlgHom.commutes,lift_t,lift_w,y,FifthSourceOverlap318.shortMap,AlgHom.comp_apply] using h
theorem w_raw:SourceOpenFractionField318.openEmbedding units w=FifthCharacterField318.root:=by
  rw [w,FifthSourceOverlap318.input_raw]
  exact FifthCharacterOrder318.embedding_root
lemma t_coordinate:t=ContactUnbranchedDifferentialFrame318.coordinate units:=rfl
end FifthOverlapCoordinates318
