module
public import FifthReciprocalFieldCoordinates318
public import FifthCharacterShortCoordinates318
public section
noncomputable section
namespace FifthShortFraction318
open FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318
set_option maxHeartbeats 700000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Order:=ShortAffineJacobian318.Ring A B
abbrev Field:=FifthCharacterField318.field
@[expose] def embedding:Order→+*Field:=
  FifthReciprocalFraction318.embedding.comp coordinateEquiv.symm.toRingHom

theorem embedding_injective:Function.Injective embedding:=
  FifthReciprocalFraction318.embedding_injective.comp coordinateEquiv.symm.injective
local instance cubicAlgebra:Algebra CubicRing Field:=FifthReciprocalFraction318.embedding.toAlgebra
local instance shortAlgebra:Algebra Order Field:=embedding.toAlgebra
/-- This literal nonsingular short ring has the actual fifth original
character subfield as its entire fraction field, through the exact coordinate map. -/
theorem actual_fractionField:IsFractionRing Order Field:=by
  letI:=FifthReciprocalFraction318.actual_fractionField
  exact IsFractionRing.of_ringEquiv_left coordinateEquiv.symm.toRingEquiv (fun _=>rfl)
theorem embedding_on_cubic (z:CubicRing):
    embedding (coordinateEquiv z)=FifthReciprocalFraction318.embedding z:=by
  change FifthReciprocalFraction318.embedding (coordinateEquiv.symm (coordinateEquiv z))=_
  rw [AlgEquiv.symm_apply_apply]
theorem embedding_x : embedding (ShortAffineJacobian318.x A B)=
    algebraMap ℚ Field (xScale:ℚ)*(FifthReciprocalFieldCoordinates318.t)⁻¹+
      algebraMap ℚ Field shift:=by
  change FifthReciprocalFraction318.embedding (coordinateEquiv.symm _)=_
  rw [FifthCharacterShortCoordinates318.inverse_x,map_add,map_mul,
    RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap]
  exact congrArg (fun z=>algebraMap ℚ Field (xScale:ℚ)*z+algebraMap ℚ Field shift)
    FifthReciprocalFieldCoordinates318.embedding_u

theorem embedding_y : embedding (ShortAffineJacobian318.y A B)=
    algebraMap ℚ Field (yScale:ℚ)*(FifthReciprocalFieldCoordinates318.t⁻¹^2*
      FifthReciprocalFieldCoordinates318.y):=by
  change FifthReciprocalFraction318.embedding (coordinateEquiv.symm _)=_
  rw [FifthCharacterShortCoordinates318.inverse_y,map_mul,RingHom.map_rat_algebraMap]
  exact congrArg (fun z=>algebraMap ℚ Field (yScale:ℚ)*z)
    FifthReciprocalFieldCoordinates318.embedding_v
end FifthShortFraction318
