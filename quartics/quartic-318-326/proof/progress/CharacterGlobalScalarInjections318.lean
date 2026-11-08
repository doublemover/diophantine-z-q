module
public import CharacterCommonScalarInjection318
public import ContactGlobalSectionDetection318
public import CompletedCharacterRegularDescent318
public section
noncomputable section
namespace CharacterGlobalScalarInjections318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X:=ContactGlobalSmooth318.Model units
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev W:=ContactGlobalSectionDetection318.common units
local instance modelIntegral:IsIntegral X:=ContactProjectiveModel318.model_integral units
/-- The actual common-open unit frame detects scalar multiplication on
whole global sections; no choice of a function-field frame is made. -/
theorem multiply_injective (i:Fin 4):
    Function.Injective (fun a:Γ(X,⊤)=>a • ContactCharacterDifferentials318.differential i):=by
  intro a b h
  apply map_injective_of_isIntegral X (homOfLE (show W≤⊤ from le_top))
  apply CharacterCommonScalarInjection318.injective i
  have hh:=congrArg (M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op) h
  simpa only [Scheme.Modules.map_smul] using hh
/-- The actual regular scalar pullback is injective by its already proved
all-open trace/8 retraction. -/
theorem scalar_pullback_injective (i:Fin 4):Function.Injective (completedMap i).appTop:=by
  intro a b h
  have hh:=congrArg (CompletedCharacterRegularDescent318.averageTop i) h
  simpa only [CompletedCharacterRegularDescent318.averageTop_pullback] using hh
end CharacterGlobalScalarInjections318
