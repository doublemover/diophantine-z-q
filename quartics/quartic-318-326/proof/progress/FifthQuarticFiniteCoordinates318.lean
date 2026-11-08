module
public import FifthQuarticFinite318
public section
noncomputable section
namespace FifthQuarticFiniteCoordinates318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318
open FifthCharacterShortPolynomial318 FifthQuarticFinite318 FifthQuarticCover318
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def t:Local:=algebraMap Quartic Local parameter
@[expose] def w:Local:=algebraMap Quartic Local (AdjoinRoot.root (polynomial quartic))
theorem t_unit:IsUnit t:=IsLocalization.Away.algebraMap_isUnit parameter
lemma t_field:fieldEmbedding t=FifthReciprocalFieldCoordinates318.t:=fieldEmbedding_on_order _
lemma w_field:fieldEmbedding w=FifthReciprocalFieldCoordinates318.y:=fieldEmbedding_on_order _
lemma original_t_ne_zero:FifthReciprocalFieldCoordinates318.t≠0:=
  FifthReciprocalFraction318.parameter_image_unit.ne_zero

/-- Exact finite-chart x equation, reusable after every algebra map. -/
theorem x_relation:shortMap (ShortAffineJacobian318.x A B)*t=
    algebraMap ℚ Local (xScale:ℚ)+algebraMap ℚ Local shift*t:=by
  apply fieldEmbedding_injective
  simp only [map_mul,map_add,shortMap_field,t_field,RingHom.map_rat_algebraMap]
  rw [FifthShortFraction318.embedding_x]
  field_simp [original_t_ne_zero]

/-- Exact finite-chart y equation, with the original quartic root retained. -/
theorem y_relation:shortMap (ShortAffineJacobian318.y A B)*t^2=
    algebraMap ℚ Local (yScale:ℚ)*w:=by
  apply fieldEmbedding_injective
  simp only [map_mul,map_pow,shortMap_field,t_field,w_field,RingHom.map_rat_algebraMap]
  rw [FifthShortFraction318.embedding_y]
  field_simp [original_t_ne_zero]
end FifthQuarticFiniteCoordinates318
