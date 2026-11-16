module
public import PELOriginalCharacterFunctionField318
public import OpenFunctionFieldSquare318
public section
noncomputable section
namespace PELOriginalCharacterPullback318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318
open scoped nonZeroDivisors
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
abbrev Source:=FourRootAffineCoordinateRing318.Ring branches
abbrev Model:=FourRootGluedScheme318.scheme branches
abbrev Raw:=PELOriginalOrderedCharacterFraction318.Raw
abbrev Order (i:Fin 4):=PELOriginalCharacterFunctionField318.Order i
local instance sourceDomain:IsDomain Source:=FourRootActualGenericField318.affine_domain branches branches_injective
local instance modelIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance orderDomain (i:Fin 4):IsDomain (Order i):=
  (PELOriginalOrderedCharacterFraction318.embedding_injective i).isDomain
local instance sourceRawAlgebra:Algebra Source Raw:=(FourRootActualGenericField318.affineEmbedding branches).toAlgebra
local instance sourceRawFraction:IsFractionRing Source Raw:=
  FourRootActualFractionField318.actual_fractionField branches branches_injective
local instance sourceDominant:IsDominant (FourRootGluedScheme318.finiteChart branches):=
  FourRootSchematicDensity318.finite_dominant branches branches_injective
local instance targetChartDominant (i:Fin 4):IsDominant (WeierstrassGluing318.finiteChart (A i) (B i)):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (WeierstrassGluing318.finiteChart (A i) (B i)).isOpenEmbedding.isOpenMap⟩
local instance finiteDominant (i:Fin 4):IsDominant
    (Spec.map (CommRingCat.ofHom (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom)):=
  ⟨(PELOriginalWholeCharacterProper318.finite_chart_surjective i).denseRange⟩
local instance wholeDominant (i:Fin 4):IsDominant (morphism i):=
  PELOriginalWholeCharacterProper318.dominant i

@[expose,instance_reducible] def sourceOrderAlgebra:Algebra Source Model.functionField:=
  ActualOpenFractionField318.sourceAlgebra (FourRootGluedScheme318.finiteChart branches)
attribute [local instance] sourceOrderAlgebra
local instance targetOrderAlgebra (i:Fin 4):Algebra (Order i) (Curve i).functionField:=
  PELOriginalCharacterFunctionField318.orderAlgebra i

@[expose] def sourceEquiv:Model.functionField≃ₐ[Source]Raw:=
  ActualOpenFractionField318.equiv (FourRootGluedScheme318.finiteChart branches) Raw
/-- The actual generic-stalk pullback of the constructed global map. -/
@[expose] def pullback (i:Fin 4):(Curve i).functionField⟶Model.functionField:=
  DominantFunctionField318.map (morphism i)

lemma pullback_on_order (i:Fin 4) (x:Order i):
    pullback i (algebraMap (Order i) (Curve i).functionField x)=
      algebraMap Source Model.functionField (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i x):=
  OpenFunctionFieldSquare318.on_coefficient (FourRootGluedScheme318.finiteChart branches)
    (WeierstrassGluing318.finiteChart (A i) (B i)) (morphism i)
    (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom (on_finite i) x

/-- The native whole-function-field pullback is EXACTLY the old original
character-subfield inclusion under the coefficient-preserving identifications. -/
theorem actual_field_square (i:Fin 4):sourceEquiv.toRingHom.comp (pullback i).hom=
    PELOriginalCharacterFunctionField318.originalEmbedding i:=by
  letI:IsFractionRing (Order i) (Curve i).functionField:=
    ActualOpenFractionField318.fractionRing (WeierstrassGluing318.finiteChart (A i) (B i))
  apply IsLocalization.ringHom_ext (Order i)⁰
  apply RingHom.ext
  intro x
  change sourceEquiv (pullback i (algebraMap (Order i) (Curve i).functionField x))=
    PELOriginalCharacterFunctionField318.originalEmbedding i
      (algebraMap (Order i) (Curve i).functionField x)
  rw [pullback_on_order,sourceEquiv.commutes,PELOriginalCharacterFunctionField318.originalEmbedding_on_order]
  exact PELOriginalOrderedCharacterFraction318.embedding_square i x
end PELOriginalCharacterPullback318
