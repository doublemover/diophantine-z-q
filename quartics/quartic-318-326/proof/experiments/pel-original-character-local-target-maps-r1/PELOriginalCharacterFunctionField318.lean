module
public import PELOriginalOrderedCharacterFraction318
public import ActualOpenFractionField318
public section
noncomputable section
namespace PELOriginalCharacterFunctionField318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalWholeCharacterMorphisms318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
abbrev Order (i:Fin 4):=PELOriginalOrderedCharacterFraction318.Order i
abbrev Character (i:Fin 4):=PELOriginalOrderedCharacterFraction318.Character i
abbrev Raw:=PELOriginalOrderedCharacterFraction318.Raw
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance orderDomain (i:Fin 4):IsDomain (Order i):=
  (PELOriginalOrderedCharacterFraction318.embedding_injective i).isDomain
local instance characterAlgebra (i:Fin 4):Algebra (Order i) (Character i):=
  (PELOriginalOrderedCharacterFraction318.embedding i).toAlgebra
local instance characterFraction (i:Fin 4):IsFractionRing (Order i) (Character i):=
  PELOriginalOrderedCharacterFraction318.actual_fractionField i

@[expose,instance_reducible] def orderAlgebra (i:Fin 4):Algebra (Order i) (Curve i).functionField:=
  ActualOpenFractionField318.sourceAlgebra (WeierstrassGluing318.finiteChart (A i) (B i))
attribute [local instance] orderAlgebra

/-- The ACTUAL generic stalk of the whole ordered target, preserving the
coefficient germ of its exact finite chart, is the old original character field. -/
@[expose] def characterEquiv (i:Fin 4):(Curve i).functionField≃ₐ[Order i]Character i:=
  ActualOpenFractionField318.equiv (WeierstrassGluing318.finiteChart (A i) (B i)) (Character i)
lemma characterEquiv_on_order (i:Fin 4) (x:Order i):
    characterEquiv i (algebraMap (Order i) (Curve i).functionField x)=
      PELOriginalOrderedCharacterFraction318.embedding i x:=
  (characterEquiv i).commutes x

@[expose] def originalEmbedding (i:Fin 4):(Curve i).functionField→+*Raw:=
  (PELOriginalActualCharacterFields318.field i).subtype.comp (characterEquiv i).toRingHom
lemma originalEmbedding_on_order (i:Fin 4) (x:Order i):
    originalEmbedding i (algebraMap (Order i) (Curve i).functionField x)=
      (PELOriginalOrderedCharacterFraction318.embedding i x:Raw):=by
  change ((characterEquiv i (algebraMap (Order i) (Curve i).functionField x):Character i):Raw)=_
  rw [characterEquiv_on_order]

/-- Identity with the native geometric germ is retained, rather than
identifying only abstract fields of the same transcendence degree. -/
theorem finite_germ (i:Fin 4) (U:(Curve i).Opens) [Nonempty U]
    [Nonempty (WeierstrassGluing318.finiteChart (A i) (B i)⁻¹ᵁU)]:
    (Curve i).germToFunctionField U≫
      (OpenFunctionField318.fieldIso (WeierstrassGluing318.finiteChart (A i) (B i))).hom=
    (WeierstrassGluing318.finiteChart (A i) (B i)).app U≫
      (Spec (CommRingCat.of (Order i))).germToFunctionField
        (WeierstrassGluing318.finiteChart (A i) (B i)⁻¹ᵁU):=
  ActualOpenFractionField318.generic_germ _ U
end PELOriginalCharacterFunctionField318
