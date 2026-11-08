module
public import CompletedCharacterNormalizationJoin318
public import CommonOpenFunctionField318
public section
noncomputable section
namespace CompletedNormalizationBirational318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterNormalizationJoin318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance originalIntegral (i:Fin 4):IsIntegral (SourceCharacterGlobal318.Model i):=
  SourceCharacterGlobal318.model_integral i
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance cubicDomain (i:Fin 4):IsDomain (SourceCharacterAlgebra318.Cubic i):=
  (CubicCharacterFraction318.embedding_injective i).isDomain
local instance cubicOpen (i:Fin 4):IsOpenImmersion (SourceCharacterGlobal318.coverMap i).toNormalization:=
  SourceCharacterGlobal318.cubicOpen_open i
local instance comparisonSurjective (i:Fin 4):Surjective (comparison i):=comparison_surjective i

/-- The actual generic-stalk pullback of the canonical comparison is an
isomorphism, proved from its exact whole cubic-chart restriction. -/
theorem comparison_generic_isIso (i:Fin 4):IsIso (DominantFunctionField318.map (comparison i)):=
  CommonOpenFunctionField318.actual_generic_iso
    (SourceCharacterGlobal318.coverMap i).toNormalization (CubicCompletedAffine318.embedding i)
    (comparison i) (comparison_on_cubic i)

/-- This is the actual generic-stalk isomorphism of comparison, not an
independently chosen function-field isomorphism. -/
@[expose] def genericIso (i:Fin 4):(Target i).functionField≅(SourceCharacterGlobal318.Model i).functionField:=by
  letI:=comparison_generic_isIso i
  exact asIso (DominantFunctionField318.map (comparison i))
lemma genericIso_hom (i:Fin 4):(genericIso i).hom=DominantFunctionField318.map (comparison i):=rfl
end CompletedNormalizationBirational318
