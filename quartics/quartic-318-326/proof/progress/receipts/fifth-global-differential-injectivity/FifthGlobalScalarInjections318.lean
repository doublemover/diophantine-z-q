module
public import FifthCommonScalarInjection318
public import ContactGlobalSectionDetection318
public import FifthCompletedDegree318
public section
noncomputable section
namespace FifthGlobalScalarInjections318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapDominant:IsDominant FifthCompletedGlobal318.map:=FifthCompletedProper318.dominant
local instance targetTop:Nonempty (⊤:Target.Opens):=⟨⟨genericPoint Target,trivial⟩⟩
local instance sourcePreimageTop:Nonempty (FifthCompletedGlobal318.map⁻¹ᵁ(⊤:Target.Opens)):=
  ⟨⟨genericPoint Model,trivial⟩⟩
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev W:=ContactGlobalSectionDetection318.common units
/-- Multiplication by the actual fifth pulled invariant detects global
regular source functions, using its actual common-open unit frame. -/
theorem multiply_injective:Function.Injective (fun a:Γ(Model,⊤)=>a • FifthActualDifferential318.differential):=by
  intro a b h
  apply map_injective_of_isIntegral Model (homOfLE (show W≤⊤ from le_top))
  apply FifthCommonScalarInjection318.injective
  have hh:=congrArg (M.presheaf.map (homOfLE (show W≤⊤ from le_top)).op) h
  simpa only [Scheme.Modules.map_smul] using hh
/-- Actual global scalar pullback is injective by its genuine dominant
generic-stalk pullback and the original integral target germ injection. -/
theorem scalar_pullback_injective:Function.Injective FifthCompletedGlobal318.map.appTop:=by
  intro a b h
  apply Target.germToFunctionField_injective ⊤
  apply FifthCompletedDegree318.pullback.hom.injective
  have ha:=congrArg (fun f=>f a) (DominantFunctionField318.map_germ FifthCompletedGlobal318.map ⊤)
  have hb:=congrArg (fun f=>f b) (DominantFunctionField318.map_germ FifthCompletedGlobal318.map ⊤)
  change FifthCompletedDegree318.pullback (Target.germToFunctionField ⊤ a)=
    Model.germToFunctionField (FifthCompletedGlobal318.map⁻¹ᵁ⊤) (FifthCompletedGlobal318.map.appTop a) at ha
  change FifthCompletedDegree318.pullback (Target.germToFunctionField ⊤ b)=
    Model.germToFunctionField (FifthCompletedGlobal318.map⁻¹ᵁ⊤) (FifthCompletedGlobal318.map.appTop b) at hb
  exact ha.trans ((congrArg (Model.germToFunctionField (FifthCompletedGlobal318.map⁻¹ᵁ⊤)) h).trans hb.symm)
end FifthGlobalScalarInjections318
