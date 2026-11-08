module
public import FifthCompletedFunctionField318
public import OpenFunctionFieldSquare318
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace FifthCompletedDegree318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthCompletedFunctionField318
open scoped nonZeroDivisors
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance orderDomain:IsDomain Order:=FifthShortFraction318.embedding_injective.isDomain
local instance infinityDomain:IsDomain Infinity:=InfinityOpenChart318.openOrder_domain units
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
attribute [local instance] targetAlgebra sourceAlgebra
local instance infinityNonempty:Nonempty (ReciprocalInfinityNormalization318.neighborhood units):=by
  change Nonempty (Spec (CommRingCat.of Infinity))
  infer_instance
local instance finiteNonempty:Nonempty (ShortAffineScheme318.scheme A B):=by
  change Nonempty (Spec (CommRingCat.of Order))
  infer_instance
local instance sourceChartDominant:IsDominant (InfinityGlobalScheme318.chartEmbedding units):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (InfinityGlobalScheme318.chartEmbedding units).isOpenEmbedding.isOpenMap⟩
local instance targetChartDominant:IsDominant (WeierstrassGluing318.finiteChart A B):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (WeierstrassGluing318.finiteChart A B).isOpenEmbedding.isOpenMap⟩
local instance chartMapDominant:IsDominant
    (Spec.map (CommRingCat.ofHom FifthSourceInfinityAlgebra318.shortMap.toRingHom)):=
  FifthCompletedProper318.infinityFinite_dominant
local instance mapDominant:IsDominant FifthCompletedGlobal318.map:=FifthCompletedProper318.dominant
/-- The actual generic-stalk pullback of the actual global fifth map. -/
@[expose] def pullback:Target.functionField⟶Model.functionField:=
  DominantFunctionField318.map FifthCompletedGlobal318.map
lemma pullback_on_order (x:Order):pullback (algebraMap Order Target.functionField x)=
    algebraMap Infinity Model.functionField (FifthSourceInfinityAlgebra318.shortMap x):=
  OpenFunctionFieldSquare318.on_coefficient (InfinityGlobalScheme318.chartEmbedding units)
    (WeierstrassGluing318.finiteChart A B) FifthCompletedGlobal318.map
    FifthSourceInfinityAlgebra318.shortMap.toRingHom FifthCompletedGlobal318.on_infinity x
/-- Exact comparison of whole actual generic-stalk maps with the original
fifth-character subfield inclusion; no degree-only identification. -/
theorem actual_field_square:sourceEquiv.toRingHom.comp pullback.hom=originalEmbedding:=by
  letI:IsFractionRing Order Target.functionField:=
    ActualOpenFractionField318.fractionRing (WeierstrassGluing318.finiteChart A B)
  apply IsLocalization.ringHom_ext Order⁰
  apply RingHom.ext
  intro x
  change sourceEquiv (pullback (algebraMap Order Target.functionField x))=
    originalEmbedding (algebraMap Order Target.functionField x)
  rw [pullback_on_order,source_on_order,original_on_order]
  exact RingHom.congr_fun FifthSourceInfinityAlgebra318.original_field_square x
@[expose,instance_reducible] def pullbackAlgebra:Algebra Target.functionField Model.functionField:=
  pullback.hom.toAlgebra
attribute [local instance] pullbackAlgebra
/-- Degree eight uses exactly the scalar action of the constructed morphism's
actual generic-stalk pullback, not a separately chosen abstract field action. -/
theorem actual_generic_degree_eight:Module.finrank Target.functionField Model.functionField=8:=by
  have hc:(algebraMap Character Raw).comp targetEquiv.toRingHom=
      sourceEquiv.toRingHom.comp (algebraMap Target.functionField Model.functionField):=
    actual_field_square.symm
  exact (Algebra.finrank_eq_of_equiv_equiv targetEquiv.toRingEquiv sourceEquiv.toRingEquiv hc).trans
    FifthCharacterField318.relative_degree_eight
end FifthCompletedDegree318
