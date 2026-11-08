module
public import ActualOpenFractionField318
public import CompletedCharacterProper318
public import PublishedCharacterFraction318
public section
noncomputable section
namespace CompletedCharacterFunctionField318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Order (i:Fin 4):=PublishedCharacterFraction318.Order i
abbrev Character (i:Fin 4):=PublishedCharacterFraction318.Field i
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance orderDomain (i:Fin 4):IsDomain (Order i):=
  (PublishedCharacterFraction318.embedding_injective i).isDomain
local instance affineIntegral (i:Fin 4):IsIntegral
    (ShortAffineScheme318.scheme (publishedA i) (publishedB i)):=by
  change IsIntegral (Spec (CommRingCat.of (Order i)))
  infer_instance
local instance characterAlgebra (i:Fin 4):Algebra (Order i) (Character i):=
  (PublishedCharacterFraction318.embedding i).toAlgebra
local instance characterFraction (i:Fin 4):IsFractionRing (Order i) (Character i):=
  PublishedCharacterFraction318.actual_fractionField i
@[expose,instance_reducible] def orderAlgebra (i:Fin 4):Algebra (Order i) (Target i).functionField:=
  ActualOpenFractionField318.sourceAlgebra (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
attribute [local instance] orderAlgebra
/-- The actual generic stalk of the literal completed target is the entire
specified character subfield of the original contact field. -/
@[expose] def characterEquiv (i:Fin 4):(Target i).functionField≃ₐ[Order i]Character i:=
  ActualOpenFractionField318.equiv (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)) (Character i)
theorem characterEquiv_on_order (i:Fin 4) (a:Order i):
    characterEquiv i (algebraMap (Order i) (Target i).functionField a)=
      PublishedCharacterFraction318.embedding i a:=
  (characterEquiv i).commutes a

/-- The specified original-field inclusion, with no change of character. -/
@[expose] def originalEmbedding (i:Fin 4):(Target i).functionField→+*
    KummerTensorField318.Raw (SourceKummerField318.parameter units):=
  (SourceCharacterFields318.field units i).subtype.comp (characterEquiv i).toRingHom

theorem originalEmbedding_on_order (i:Fin 4) (a:Order i):
    originalEmbedding i (algebraMap (Order i) (Target i).functionField a)=
      (PublishedCharacterFraction318.embedding i a : KummerTensorField318.Raw (SourceKummerField318.parameter units)):=by
  change ((characterEquiv i (algebraMap (Order i) (Target i).functionField a):Character i):
    KummerTensorField318.Raw (SourceKummerField318.parameter units))=_
  rw [characterEquiv_on_order]

/-- Compatibility with actual germs through the actual finite-chart stalk
isomorphism fixes the geometric source of this field identification. -/
theorem finite_germ (i:Fin 4) (U:(Target i).Opens) [Nonempty U]
    [Nonempty (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)⁻¹ᵁU)]:
    (Target i).germToFunctionField U≫
      (OpenFunctionField318.fieldIso (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))).hom=
    (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).app U≫
      (Spec (CommRingCat.of (Order i))).germToFunctionField
        (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)⁻¹ᵁU):=
  ActualOpenFractionField318.generic_germ _ U
end CompletedCharacterFunctionField318
