module
public import FifthOpenTrace318
public import FifthTraceProjection318
public section
noncomputable section
namespace FifthRegularScalarDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapDominant:IsDominant FifthCompletedGlobal318.map:=FifthCompletedProper318.dominant
local instance modelTop:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
local instance sourcePreimageTop:Nonempty (FifthCompletedGlobal318.map⁻¹ᵁ(⊤:Target.Opens)):=
  ⟨⟨genericPoint Model,trivial⟩⟩
local instance targetTop:Nonempty (⊤:Target.Opens):=⟨⟨genericPoint Target,trivial⟩⟩
@[expose] def traceTop:Γ(Model,⊤)→+Γ(Target,⊤):=FifthOpenTrace318.trace ⊤
lemma traceTop_generic (r:Γ(Model,⊤)):
    Target.germToFunctionField ⊤ (traceTop r)=FifthGenericTrace318.trace (Model.germToFunctionField ⊤ r):=
  FifthOpenTrace318.original_generic_trace ⊤ r
@[expose] def constants:ℚ→+*Γ(Target,⊤):=
  (WeierstrassGluing318.structureMap A B).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
lemma eight_unit:IsUnit (8:Γ(Target,⊤)):=by
  simpa only [map_ofNat] using (IsUnit.mk0 (8:ℚ) (by norm_num)).map constants
@[expose] def inverseEight:Γ(Target,⊤):=↑(eight_unit.unit⁻¹)
lemma eight_inverse:(8:Γ(Target,⊤))*inverseEight=1:=by
  rw [←eight_unit.unit_spec]
  exact Units.mul_inv _
/-- A globally regular source scalar whose actual generic germ lies in the
actual quotient field descends as a globally regular target scalar. The
construction uses the genuine all-open regular trace and division by 8. -/
theorem exists_target (r:Γ(Model,⊤))
    (h:Set.range FifthCompletedDegree318.pullback (Model.germToFunctionField ⊤ r)):
    ∃g:Γ(Target,⊤),FifthCompletedGlobal318.map.appTop g=r:=by
  obtain ⟨z,hz⟩:=h
  let g:Γ(Target,⊤):=inverseEight*traceTop r
  have h8:(8:Γ(Target,⊤))*g=traceTop r:=by
    change (8:Γ(Target,⊤))*(inverseEight*traceTop r)=traceTop r
    rw [←mul_assoc,eight_inverse,one_mul]
  have hg:Target.germToFunctionField ⊤ g=z:=by
    have hh:=congrArg (Target.germToFunctionField ⊤) h8
    rw [map_mul,map_ofNat,traceTop_generic,←hz,
      FifthGenericTrace318.trace_pullback] at hh
    have hne:(8:Target.functionField)≠0:=by
      have hu:=eight_unit.map (Target.germToFunctionField ⊤).hom
      simpa only [map_ofNat] using hu.ne_zero
    exact mul_left_cancel₀ hne hh
  refine ⟨g,?_⟩
  apply Model.germToFunctionField_injective ⊤
  have hn:=congrArg (fun q=>q g) (DominantFunctionField318.map_germ FifthCompletedGlobal318.map ⊤)
  change FifthCompletedDegree318.pullback (Target.germToFunctionField ⊤ g)=
    Model.germToFunctionField ⊤ (FifthCompletedGlobal318.map.appTop g) at hn
  rw [←hn,hg]
  exact hz
end FifthRegularScalarDescent318
