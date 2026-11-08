module
public import FifthCompletedProper318
public import ActualOpenFractionField318
public section
noncomputable section
namespace FifthCompletedFunctionField318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Order:=FifthShortFraction318.Order
abbrev Character:=FifthCharacterField318.field
abbrev Infinity:=InfinityOpenChart318.OpenOrder units
abbrev Model:=ContactGlobalSmooth318.Model units
abbrev Raw:=FifthCharacterField318.L
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance orderDomain:IsDomain Order:=FifthShortFraction318.embedding_injective.isDomain
local instance infinityDomain:IsDomain Infinity:=InfinityOpenChart318.openOrder_domain units
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
local instance characterFraction:IsFractionRing Order Character:=FifthShortFraction318.actual_fractionField
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance originalFraction:IsFractionRing Infinity Raw:=InfinityOpenFractionField318.open_fractionField units
@[expose,instance_reducible] def targetAlgebra:Algebra Order Target.functionField:=
  ActualOpenFractionField318.sourceAlgebra (WeierstrassGluing318.finiteChart A B)
@[expose,instance_reducible] def sourceAlgebra:Algebra Infinity Model.functionField:=
  ActualOpenFractionField318.sourceAlgebra (InfinityGlobalScheme318.chartEmbedding units)
attribute [local instance] targetAlgebra sourceAlgebra
/-- Identification through the actual finite-chart generic-stalk map. -/
@[expose] def targetEquiv:Target.functionField≃ₐ[Order]Character:=
  ActualOpenFractionField318.equiv (WeierstrassGluing318.finiteChart A B) Character
/-- Identification through the actual whole infinity-chart generic-stalk map. -/
@[expose] def sourceEquiv:Model.functionField≃ₐ[Infinity]Raw:=
  ActualOpenFractionField318.equiv (InfinityGlobalScheme318.chartEmbedding units) Raw
lemma target_on_order (x:Order):targetEquiv (algebraMap Order Target.functionField x)=
    FifthShortFraction318.embedding x:=targetEquiv.commutes x
lemma source_on_order (x:Infinity):sourceEquiv (algebraMap Infinity Model.functionField x)=
    InfinityOpenFractionField318.openEmbedding units x:=sourceEquiv.commutes x
@[expose] def originalEmbedding:Target.functionField→+*Raw:=
  FifthCharacterField318.field.subtype.comp targetEquiv.toRingHom
lemma original_on_order (x:Order):originalEmbedding (algebraMap Order Target.functionField x)=
    (FifthShortFraction318.embedding x:Raw):=by
  change (targetEquiv (algebraMap Order Target.functionField x):Raw)=_
  rw [target_on_order]
end FifthCompletedFunctionField318
