module
public import OpenUnitNorm318
public import CompletedCharacterTraceBasis318
public section
noncomputable section
namespace CompletedCharacterOpenNorm318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
/-- Genuine norm of regular functions on every original target open for
all four unchanged completed character maps. -/
@[expose] def norm (i:Fin 4) (U:(Target i).Opens):
    Γ(Model,completedMap i⁻¹ᵁU)→*Γ(Target i,U):=
  OpenDominantNorm318.norm (completedMap i) (hasBasis i) U
lemma restrict (i:Fin 4) {U V:(Target i).Opens} (j:U⟶V)
    (s:Γ(Model,completedMap i⁻¹ᵁV)):
    (Target i).presheaf.map j.op (norm i V s)=norm i U
      (Model.presheaf.map (homOfLE ((completedMap i).preimage_mono j.le)).op s):=
  OpenDominantNorm318.restrict (completedMap i) (hasBasis i) j s
/-- The scalar structure is the actual original generic-stalk pullback,
not a separately assigned degree-eight inclusion. -/
lemma original_generic_norm (i:Fin 4) (U:(Target i).Opens) [Nonempty U]
    (s:Γ(Model,completedMap i⁻¹ᵁU)):
    letI:Nonempty (completedMap i⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty (completedMap i) U
    letI:=CompletedCharacterDegree318.pullbackAlgebra i
    (Target i).germToFunctionField U (norm i U s)=
      Algebra.norm (Target i).functionField (Model.germToFunctionField (completedMap i⁻¹ᵁU) s):=
  OpenDominantNorm318.norm_embedding (completedMap i) (hasBasis i) U s
/-- The exact eighth-power identity on every actual open, including empty opens. -/
lemma pullback (i:Fin 4) (U:(Target i).Opens) (s:Γ(Target i,U)):
    norm i U ((completedMap i).app U s)=s^8:=by
  change OpenDominantNorm318.norm (completedMap i) (hasBasis i) U ((completedMap i).app U s)=_
  simpa only [CompletedCharacterDegree318.actual_generic_degree_eight] using
    OpenDominantNorm318.pullback (completedMap i) (hasBasis i) U s
/-- Compatibility with the genuine normal-affine norm on each eligible
original affine open; no new chart presentation is selected. -/
lemma affine_eq (i:Fin 4) (U:(Target i).Opens) [Nonempty U]
    [IsIntegrallyClosed Γ(Target i,U)] (hU:IsAffineOpen U):
    norm i U=AffineDominantNorm318.norm (completedMap i) U hU:=
  OpenDominantNorm318.affine_eq (completedMap i) (hasBasis i) U hU
/-- Actual natural transfer on invertible regular functions. -/
@[expose] def unitNorm (i:Fin 4):OpenUnitNorm318.sourceUnits (completedMap i)⟶
    OpenUnitNorm318.targetUnits (Y:=Target i):=
  OpenUnitNorm318.norm (completedMap i) (hasBasis i)
lemma unit_value (i:Fin 4) (U:(Target i).Opens) (s:Γ(Model,completedMap i⁻¹ᵁU)ˣ):
    Units.val (α:=Γ(Target i,U)) ((unitNorm i).app (op U) s)=
      norm i U (s:Γ(Model,completedMap i⁻¹ᵁU)):=rfl
lemma unit_pullback (i:Fin 4) (U:(Target i).Opens) (s:Γ(Target i,U)ˣ):
    (unitNorm i).app (op U) (Units.map ((completedMap i).app U).hom.toMonoidHom s)=s^8:=by
  change (OpenUnitNorm318.norm (completedMap i) (hasBasis i)).app (op U) _=_
  simpa only [CompletedCharacterDegree318.actual_generic_degree_eight] using
    OpenUnitNorm318.pullback (completedMap i) (hasBasis i) U s
end CompletedCharacterOpenNorm318
