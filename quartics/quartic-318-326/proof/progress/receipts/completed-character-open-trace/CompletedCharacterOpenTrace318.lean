module
public import CompletedCharacterTraceBasis318
public import OpenTraceSheaf318
public section
noncomputable section
namespace CompletedCharacterOpenTrace318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
local instance mapFinite (i:Fin 4):IsFinite (completedMap i):=
  CompletedCharacterFinite318.completedMap_finite i
/-- Genuine regular-function trace on every original open for all four maps. -/
@[expose] def trace (i:Fin 4) (U:(Target i).Opens):Γ(Model,completedMap i⁻¹ᵁU)→+Γ(Target i,U):=
  OpenDominantTrace318.trace (completedMap i) (hasBasis i) (generic_finite i) U
lemma original_generic_trace (i:Fin 4) (U:(Target i).Opens) [Nonempty U]
    (s:Γ(Model,completedMap i⁻¹ᵁU)):
    letI:Nonempty (completedMap i⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty (completedMap i) U
    letI:=CompletedCharacterDegree318.pullbackAlgebra i
    (Target i).germToFunctionField U (trace i U s)=
      Algebra.trace (Target i).functionField Model.functionField
        (Model.germToFunctionField (completedMap i⁻¹ᵁU) s):=
  OpenDominantTrace318.trace_embedding (completedMap i) (hasBasis i) (generic_finite i) U s
lemma restrict (i:Fin 4) {U V:(Target i).Opens} (j:U⟶V) (s:Γ(Model,completedMap i⁻¹ᵁV)):
    (Target i).presheaf.map j.op (trace i V s)=trace i U
      (Model.presheaf.map (homOfLE ((completedMap i).preimage_mono j.le)).op s):=
  OpenDominantTrace318.restrict (completedMap i) (hasBasis i) (generic_finite i) j s
lemma trace_pullback (i:Fin 4) (U:(Target i).Opens) (s:Γ(Target i,U)):
    trace i U ((completedMap i).app U s)=8*s:=by
  have h:=OpenDominantTrace318.pullback (completedMap i) (hasBasis i) (generic_finite i) U s
  simpa only [trace,CompletedCharacterDegree318.actual_generic_degree_eight,nsmul_eq_mul,Nat.cast_ofNat] using h
lemma linearity (i:Fin 4) (U:(Target i).Opens) (a:Γ(Target i,U)) (s:Γ(Model,completedMap i⁻¹ᵁU)):
    trace i U ((completedMap i).app U a*s)=a*trace i U s:=
  OpenDominantTrace318.linearity (completedMap i) (hasBasis i) (generic_finite i) U a s
@[expose] def transfer (i:Fin 4):
    OpenTraceSheaf318.source (completedMap i)⟶OpenTraceSheaf318.target (Y:=Target i):=
  OpenTraceSheaf318.transfer (completedMap i) (hasBasis i) (generic_finite i)
lemma transfer_component (i:Fin 4) (U:(Target i).Opens) (s:Γ(Model,completedMap i⁻¹ᵁU)):
    (transfer i).app (Opposite.op U) s=trace i U s:=rfl
end CompletedCharacterOpenTrace318
