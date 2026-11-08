module
public import CompletedCharacterTraceAverage318
public section
noncomputable section
namespace CompletedCharacterRegularDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterTraceBasis318
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance mapDominant (i:Fin 4):IsDominant (completedMap i):=
  CompletedCharacterProper318.completedMap_dominant i
local instance modelTop:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
local instance sourcePreimageTop (i:Fin 4):Nonempty (completedMap i⁻¹ᵁ(⊤:(Target i).Opens)):=
  ⟨⟨genericPoint Model,trivial⟩⟩
local instance targetTop (i:Fin 4):Nonempty (⊤:(Target i).Opens):=⟨⟨genericPoint (Target i),trivial⟩⟩
local instance actualAlgebra (i:Fin 4):Algebra (Target i).functionField Model.functionField:=
  CompletedCharacterDegree318.pullbackAlgebra i
@[expose] def averageTop (i:Fin 4):Γ(Model,⊤)→+Γ(Target i,⊤):=
  CompletedCharacterTraceAverage318.average i ⊤
lemma averageTop_pullback (i:Fin 4) (g:Γ(Target i,⊤)):
    averageTop i ((completedMap i).appTop g)=g:=
  CompletedCharacterTraceAverage318.average_pullback i ⊤ g
lemma traceTop_generic (i:Fin 4) (r:Γ(Model,⊤)):
    (Target i).germToFunctionField ⊤ (CompletedCharacterOpenTrace318.trace i ⊤ r)=
      Algebra.trace (Target i).functionField Model.functionField (Model.germToFunctionField ⊤ r):=
  CompletedCharacterOpenTrace318.original_generic_trace i ⊤ r
lemma eight_average (i:Fin 4) (r:Γ(Model,⊤)):
    (8:Γ(Target i,⊤))*averageTop i r=CompletedCharacterOpenTrace318.trace i ⊤ r:=by
  change 8*(CompletedCharacterTraceAverage318.scalar i ⊤ (1/8)*CompletedCharacterOpenTrace318.trace i ⊤ r)=_
  rw [mul_left_comm,←mul_assoc,CompletedCharacterTraceAverage318.eighth_mul,one_mul]
lemma generic_trace_pullback (i:Fin 4) (z:(Target i).functionField):
    Algebra.trace (Target i).functionField Model.functionField
      (CompletedCharacterPullback318.pullback i z)=8*z:=by
  change Algebra.trace (Target i).functionField Model.functionField
    (algebraMap (Target i).functionField Model.functionField z)=8*z
  have h:=Algebra.trace_algebraMap (R:=(Target i).functionField) (S:=Model.functionField) z
  simpa only [CompletedCharacterDegree318.actual_generic_degree_eight,nsmul_eq_mul,Nat.cast_ofNat] using h
/-- The actual regular trace/8 has precisely the supplied target generic
value whenever the original source germ is its genuine pullback. -/
lemma averageTop_generic (i:Fin 4) (r:Γ(Model,⊤)) (z:(Target i).functionField)
    (hz:CompletedCharacterPullback318.pullback i z=Model.germToFunctionField ⊤ r):
    (Target i).germToFunctionField ⊤ (averageTop i r)=z:=by
  have hh:=congrArg ((Target i).germToFunctionField ⊤) (eight_average i r)
  rw [map_mul,map_ofNat,traceTop_generic,←hz,
    generic_trace_pullback] at hh
  have hu:IsUnit (8:Γ(Target i,⊤)):=by
    simpa only [map_ofNat] using (IsUnit.mk0 (8:ℚ) (by norm_num)).map
      (CompletedCharacterTraceAverage318.scalar i ⊤)
  have hne:(8:(Target i).functionField)≠0:=by
    have hu':=hu.map ((Target i).germToFunctionField ⊤).hom
    simpa only [map_ofNat] using hu'.ne_zero
  exact mul_left_cancel₀ hne hh
/-- Genuine global regular-function descent through each unchanged quotient
map, using its actual generic-stalk range and actual trace/8. -/
lemma pullback_average (i:Fin 4) (r:Γ(Model,⊤))
    (h:Set.range (CompletedCharacterPullback318.pullback i) (Model.germToFunctionField ⊤ r)):
    (completedMap i).appTop (averageTop i r)=r:=by
  obtain ⟨z,hz⟩:=h
  apply Model.germToFunctionField_injective ⊤
  have hn:=congrArg (fun q=>q (averageTop i r)) (DominantFunctionField318.map_germ (completedMap i) ⊤)
  change CompletedCharacterPullback318.pullback i ((Target i).germToFunctionField ⊤ (averageTop i r))=
    Model.germToFunctionField ⊤ ((completedMap i).appTop (averageTop i r)) at hn
  rw [←hn,averageTop_generic i r z hz]
  exact hz
lemma exists_target (i:Fin 4) (r:Γ(Model,⊤))
    (h:Set.range (CompletedCharacterPullback318.pullback i) (Model.germToFunctionField ⊤ r)):
    ∃g:Γ(Target i,⊤),(completedMap i).appTop g=r:=⟨averageTop i r,pullback_average i r h⟩
lemma existsUnique_target (i:Fin 4) (r:Γ(Model,⊤))
    (h:Set.range (CompletedCharacterPullback318.pullback i) (Model.germToFunctionField ⊤ r)):
    ∃!g:Γ(Target i,⊤),(completedMap i).appTop g=r:=by
  refine ⟨averageTop i r,pullback_average i r h,?_⟩
  intro g hg
  have hh:=congrArg (averageTop i) hg
  rw [averageTop_pullback] at hh
  exact hh
end CompletedCharacterRegularDescent318
