module
public import CompletedCharacterPullback318
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace CompletedCharacterDegree318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterPullback318
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance sourceOrderAlgebra:Algebra Source Model.functionField:=
  CompletedCharacterPullback318.sourceOrderAlgebra
local instance targetOrderAlgebra (i:Fin 4):Algebra
    (CompletedCharacterFunctionField318.Order i) (Target i).functionField:=
  CompletedCharacterFunctionField318.orderAlgebra i
local instance sourceRawAlgebra:Algebra Source Raw:=
  (ContactKummerOrder318.embedding units).toAlgebra
local instance characterOrderAlgebra (i:Fin 4):Algebra
    (CompletedCharacterFunctionField318.Order i) (CompletedCharacterFunctionField318.Character i):=
  (PublishedCharacterFraction318.embedding i).toAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
abbrev Character (i:Fin 4):=SourceCharacterFields318.field units i

/-- The original full contact field has degree eight over the specified
quadratic character subfield. -/
theorem character_degree_eight (i:Fin 4):Module.finrank (Character i) Raw=8:=by
  have h:=Module.finrank_mul_finrank (RatFunc ℚ) (Character i) Raw
  rw [SourceCharacterFields318.degree_two units i,KummerTensorField318.source_raw_degree units] at h
  omega

/-- The scalar action here is the actual generic-stalk pullback of the
constructed global completedMap, not a separately assigned field inclusion. -/
@[expose,instance_reducible] def pullbackAlgebra (i:Fin 4):
    Algebra (Target i).functionField Model.functionField := (pullback i).hom.toAlgebra
attribute [local instance] pullbackAlgebra

/-- Generic degree eight of the actual global completed-character morphism,
with both actual generic stalks and its actual pullback scalar structure. -/
theorem actual_generic_degree_eight (i:Fin 4):
    Module.finrank (Target i).functionField Model.functionField=8:=by
  have hc:(algebraMap (Character i) Raw).comp
      (CompletedCharacterFunctionField318.characterEquiv i).toRingHom=
    sourceEquiv.toRingHom.comp (algebraMap (Target i).functionField Model.functionField):=
    (actual_field_square i).symm
  exact (Algebra.finrank_eq_of_equiv_equiv
    (CompletedCharacterFunctionField318.characterEquiv i).toRingEquiv
    sourceEquiv.toRingEquiv hc).trans (character_degree_eight i)
end CompletedCharacterDegree318
