module
public import OpenFunctionFieldSquare318
public import CompletedCharacterFunctionField318
public section
noncomputable section
namespace CompletedCharacterPullback318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
open scoped nonZeroDivisors
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Source:=ContactKummerOrder318.SourceOrder units
abbrev Model:=ContactGlobalSmooth318.Model units
abbrev Raw:=SourceFractionField318.L units
abbrev Order (i:Fin 4):=CompletedCharacterFunctionField318.Order i
local instance sourceDomain:IsDomain Source:=ContactKummerOrder318.source_domain units
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance orderDomain (i:Fin 4):IsDomain (Order i):=
  (PublishedCharacterFraction318.embedding_injective i).isDomain
local instance affineIntegral (i:Fin 4):IsIntegral
    (ShortAffineScheme318.scheme (publishedA i) (publishedB i)):=by
  change IsIntegral (Spec (CommRingCat.of (Order i)))
  infer_instance
local instance sourceRawAlgebra:Algebra Source Raw:=(ContactKummerOrder318.embedding units).toAlgebra
local instance sourceRawFraction:IsFractionRing Source Raw:=SourceFractionField318.actual_fractionField units
local instance sourceDominant:IsDominant (SourceGlobalAffine318.chartEmbedding units):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (SourceGlobalAffine318.chartEmbedding units).isOpenEmbedding.isOpenMap⟩
local instance targetChartDominant (i:Fin 4):IsDominant
    (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).isOpenEmbedding.isOpenMap⟩
local instance finiteDominant (i:Fin 4):IsDominant
    (Spec.map (CommRingCat.ofHom (SourceCharacterAlgebra318.publishedToSource i).toRingHom)):=by
  change IsDominant (SourceCharacterAffine318.publishedMap i)
  exact ⟨(SourceCharacterAffine318.publishedMap_surjective i).denseRange⟩
local instance completedDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i

@[expose,instance_reducible] def sourceOrderAlgebra:Algebra Source Model.functionField:=
  ActualOpenFractionField318.sourceAlgebra (SourceGlobalAffine318.chartEmbedding units)
attribute [local instance] sourceOrderAlgebra
local instance targetOrderAlgebra (i:Fin 4):Algebra (Order i) (Target i).functionField:=
  CompletedCharacterFunctionField318.orderAlgebra i

/-- The actual source generic stalk with the original full contact field. -/
@[expose] def sourceEquiv:Model.functionField≃ₐ[Source]Raw:=
  ActualOpenFractionField318.equiv (SourceGlobalAffine318.chartEmbedding units) Raw
/-- This is the actual generic-stalk pullback of the constructed global map. -/
@[expose] def pullback (i:Fin 4):(Target i).functionField⟶Model.functionField:=
  DominantFunctionField318.map (completedMap i)

theorem pullback_on_order (i:Fin 4) (a:Order i):
    pullback i (algebraMap (Order i) (Target i).functionField a)=
      algebraMap Source Model.functionField (SourceCharacterAlgebra318.publishedToSource i a):=
  OpenFunctionFieldSquare318.on_coefficient (SourceGlobalAffine318.chartEmbedding units)
    (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
    (completedMap i) (SourceCharacterAlgebra318.publishedToSource i).toRingHom (on_finite i) a

/-- The whole actual generic-stalk pullback is exactly the original
character-subfield inclusion under the specified full-field identifications. -/
theorem actual_field_square (i:Fin 4):
    sourceEquiv.toRingHom.comp (pullback i).hom=
      CompletedCharacterFunctionField318.originalEmbedding i:=by
  letI:IsFractionRing (Order i) (Target i).functionField:=
    ActualOpenFractionField318.fractionRing (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))
  apply IsLocalization.ringHom_ext (Order i)⁰
  apply RingHom.ext
  intro a
  change sourceEquiv (pullback i (algebraMap (Order i) (Target i).functionField a))=
    CompletedCharacterFunctionField318.originalEmbedding i (algebraMap (Order i) (Target i).functionField a)
  rw [pullback_on_order,sourceEquiv.commutes,CompletedCharacterFunctionField318.originalEmbedding_on_order]
  exact SourceCharacterAlgebra318.toSource_embedding i ((CubicPublishedScheme318.coordinateEquiv i).symm a)
end CompletedCharacterPullback318
