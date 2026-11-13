module
public import PELOriginalNativeCharacterFixedField318
public import NormalFiniteImageDetection318
public section
noncomputable section
namespace PELOriginalCharacterAffineImage318
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalActualCharacterFields318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
abbrev Order (i:Fin 4):=PELOriginalOrderedCharacterFraction318.Order i
abbrev Source:=FourRootAffineCoordinateRing318.Ring branches
abbrev Character (i:Fin 4):=PELOriginalOrderedCharacterFraction318.Character i
abbrev Raw:=PELOriginalOrderedCharacterFraction318.Raw

local instance orderAlgebra (i:Fin 4):Algebra (Order i) (Character i):=
  (PELOriginalOrderedCharacterFraction318.embedding i).toAlgebra
local instance orderFraction (i:Fin 4):IsFractionRing (Order i) (Character i):=
  PELOriginalOrderedCharacterFraction318.actual_fractionField i
local instance sourceAlgebra (i:Fin 4):Algebra (Order i) Source:=
  (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom.toAlgebra
local instance rawAlgebra (i:Fin 4):Algebra (Order i) Raw:=
  ((field i).subtype.comp (PELOriginalOrderedCharacterFraction318.embedding i)).toAlgebra
local instance rawTower (i:Fin 4):IsScalarTower (Order i) (Character i) Raw:=
  IsScalarTower.of_algebraMap_eq (fun _=>rfl)
local instance sourceFinite (i:Fin 4):Module.Finite (Order i) Source:=
  RingHom.finite_algebraMap.mp (PELOriginalOrderedCharacterSchemeMaps318.finite_ring i)
local instance orderNormal (i:Fin 4):IsIntegrallyClosed (Order i):=by
  have hD:IsUnit (-16*(4*(A i)^3+27*(B i)^2)):=
    isUnit_iff_ne_zero.mpr (NormalizedLegendreProjectiveModel318.discriminant_ne
      (PELOriginalOrderedCharacterCoordinate318.parameter i)
      (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).1
      (PELOriginalOrderedCharacterCoordinate318.parameter_nonexceptional i).2)
  letI:=FieldWeierstrassDedekind318.affine (A i) (B i) hD
  infer_instance

/-- The common overfield embedding is the ORIGINAL full affine embedding,
now checked as an algebra map for this specific target coordinate action. -/
@[expose] def sourceEmbedding (i:Fin 4):Source→ₐ[Order i]Raw where
  __:=FourRootActualGenericField318.affineEmbedding branches
  commutes':=PELOriginalOrderedCharacterFraction318.embedding_square i
@[expose] def characterEmbedding (i:Fin 4):Character i→ₐ[Order i]Raw:=
  IsScalarTower.toAlgHom (Order i) (Character i) Raw

/-- Whole finite-chart image, including every branch: regular functions
come from the exact target iff their original field images lie in the
specified character field. There is no generic localization in the source. -/
theorem range_iff (i:Fin 4) (x:Source):
    x∈Set.range (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i) ↔
      FourRootActualGenericField318.affineEmbedding branches x∈field i:=by
  have h:=NormalFiniteImageDetection318.range_iff (sourceEmbedding i) (characterEmbedding i)
    (FourRootActualGenericField318.affineEmbedding_injective branches)
    (field i).subtype.injective x
  change x∈Set.range (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i) ↔
    FourRootActualGenericField318.affineEmbedding branches x∈Set.range (characterEmbedding i) at h
  rw [h]
  constructor
  · rintro ⟨z,rfl⟩
    exact z.property
  · intro hx
    exact ⟨⟨_,hx⟩,rfl⟩

theorem range_fixed_field_iff (i:Fin 4) (x:Source):
    x∈Set.range (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i) ↔
      FourRootActualGenericField318.affineEmbedding branches x∈
        IntermediateField.fixedField (field i).fixingSubgroup:=by
  rw [PELOriginalActualCharacterFields318.actual_fixed_field]
  exact range_iff i x
end PELOriginalCharacterAffineImage318
