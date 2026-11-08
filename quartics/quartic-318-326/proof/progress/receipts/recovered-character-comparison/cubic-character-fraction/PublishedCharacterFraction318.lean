module
public import CubicCharacterFraction318
public import CubicPublishedScheme318
public section
noncomputable section
namespace PublishedCharacterFraction318
open SourceTwistArithmetic318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Order (i:Fin 4):=ShortAffineJacobian318.Ring (publishedA i) (publishedB i)
abbrev Field (i:Fin 4):=CubicCharacterFraction318.Field i
@[expose] def embedding (i:Fin 4):Order i→+*Field i:=
  (CubicCharacterFraction318.embedding i).comp (CubicPublishedScheme318.coordinateEquiv i).symm.toRingHom

theorem embedding_injective (i:Fin 4):Function.Injective (embedding i):=
  (CubicCharacterFraction318.embedding_injective i).comp (CubicPublishedScheme318.coordinateEquiv i).symm.injective

local instance sourceAlgebra (i:Fin 4):Algebra (CubicCharacterFraction318.Order i) (Field i):=
  (CubicCharacterFraction318.embedding i).toAlgebra
local instance publishedAlgebra (i:Fin 4):Algebra (Order i) (Field i):=(embedding i).toAlgebra

/-- The literal published affine coordinate ring has the actual character
subfield of the original contact field as its entire fraction field. -/
theorem actual_fractionField (i:Fin 4):IsFractionRing (Order i) (Field i):=by
  letI:=CubicCharacterFraction318.actual_fractionField i
  exact IsFractionRing.of_ringEquiv_left (CubicPublishedScheme318.coordinateEquiv i).symm.toRingEquiv
    (fun x=>rfl)

theorem embedding_on_cubic (i:Fin 4) (z:CubicCharacterFraction318.Order i):
    embedding i (CubicPublishedScheme318.coordinateEquiv i z)=CubicCharacterFraction318.embedding i z:=by
  change CubicCharacterFraction318.embedding i ((CubicPublishedScheme318.coordinateEquiv i).symm
    (CubicPublishedScheme318.coordinateEquiv i z))=_
  rw [AlgEquiv.symm_apply_apply]

theorem field_degree_two (i:Fin 4):Module.finrank (RatFunc ℚ) (Field i)=2:=
  SourceCharacterFields318.degree_two units i
end PublishedCharacterFraction318
