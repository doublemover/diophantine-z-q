module
public import OpenTraceSheaf318
public import FifthChartTrace318
public import FifthTargetNormalBasis318
public section
noncomputable section
namespace FifthOpenTrace318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance mapFinite:IsFinite map:=FifthCompletedFinite318.finite
local instance mapDominant:IsDominant map:=FifthCompletedProper318.dominant
@[expose] def trace (U:Target.Opens):Γ(Model,map⁻¹ᵁU)→+Γ(Target,U):=
  OpenDominantTrace318.trace map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite U
lemma original_generic_trace (U:Target.Opens) [Nonempty U] (s:Γ(Model,map⁻¹ᵁU)):
    letI:Nonempty (map⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty map U
    Target.germToFunctionField U (trace U s)=
      FifthGenericTrace318.trace (Model.germToFunctionField (map⁻¹ᵁU) s):=
  OpenDominantTrace318.trace_embedding map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite U s
lemma restrict {U V:Target.Opens} (i:U⟶V) (s:Γ(Model,map⁻¹ᵁV)):
    Target.presheaf.map i.op (trace V s)=trace U
      (Model.presheaf.map (homOfLE (map.preimage_mono i.le)).op s):=
  OpenDominantTrace318.restrict map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite i s
lemma trace_pullback (U:Target.Opens) (s:Γ(Target,U)):
    trace U (map.app U s)=8*s:=by
  have h:=OpenDominantTrace318.pullback map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite U s
  simpa only [trace,FifthCompletedDegree318.actual_generic_degree_eight,nsmul_eq_mul,Nat.cast_ofNat] using h
lemma linearity (U:Target.Opens) (a:Γ(Target,U)) (s:Γ(Model,map⁻¹ᵁU)):
    trace U (map.app U a*s)=a*trace U s:=
  OpenDominantTrace318.linearity map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite U a s
lemma chart_eq (b:Bool):trace (chartOpen b)=FifthChartTrace318.trace b:=by
  letI:=chart_nonempty b
  letI:=chart_normal b
  exact OpenDominantTrace318.affine_eq map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite
    (chartOpen b) (chart_affine b)
/-- An actual natural additive transfer on every original target open. -/
@[expose] def transfer:OpenTraceSheaf318.source map⟶OpenTraceSheaf318.target (Y:=Target):=
  OpenTraceSheaf318.transfer map FifthTargetNormalBasis318.hasBasis FifthChartTrace318.generic_finite
@[simp] lemma transfer_component (U:Target.Opens) (s:Γ(Model,map⁻¹ᵁU)):
    transfer.app (Opposite.op U) s=trace U s:=rfl
end FifthOpenTrace318
