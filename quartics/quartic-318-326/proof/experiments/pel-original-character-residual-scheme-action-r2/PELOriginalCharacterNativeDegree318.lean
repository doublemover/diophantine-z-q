module
public import PELOriginalCharacterPullback318
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace PELOriginalCharacterNativeDegree318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance modelIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance sourceOrderAlgebra:Algebra Source Model.functionField:=
  PELOriginalCharacterPullback318.sourceOrderAlgebra
local instance targetOrderAlgebra (i:Fin 4):Algebra (Order i) (Curve i).functionField:=
  PELOriginalCharacterFunctionField318.orderAlgebra i
local instance sourceRawAlgebra:Algebra Source Raw:=(FourRootActualGenericField318.affineEmbedding branches).toAlgebra
local instance characterOrderAlgebra (i:Fin 4):Algebra (Order i)
    (PELOriginalCharacterFunctionField318.Character i):=
  (PELOriginalOrderedCharacterFraction318.embedding i).toAlgebra
abbrev Character (i:Fin 4):=PELOriginalActualCharacterFields318.field i

/-- The scalar action is the ACTUAL generic-stalk pullback of the
constructed global map, not an externally assigned character inclusion. -/
@[expose,instance_reducible] def pullbackAlgebra (i:Fin 4):
    Algebra (Curve i).functionField Model.functionField:=(pullback i).hom.toAlgebra
attribute [local instance] pullbackAlgebra

/-- Native generic degree eight, after checking both actual generic
stalk identifications and the complete pullback/inclusion square. -/
theorem actual_generic_degree_eight (i:Fin 4):
    Module.finrank (Curve i).functionField Model.functionField=8:=by
  have hc:(algebraMap (Character i) Raw).comp
      (PELOriginalCharacterFunctionField318.characterEquiv i).toRingHom=
    sourceEquiv.toRingHom.comp (algebraMap (Curve i).functionField Model.functionField):=
    (actual_field_square i).symm
  exact (Algebra.finrank_eq_of_equiv_equiv
    (PELOriginalCharacterFunctionField318.characterEquiv i).toRingEquiv
    sourceEquiv.toRingEquiv hc).trans (PELOriginalWholeCharacterOrders318.degree_eight i)
end PELOriginalCharacterNativeDegree318
