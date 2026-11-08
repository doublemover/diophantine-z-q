module
public import FifthChartNorm318
public import FifthGenericTrace318
public import FifthTraceCharacters318
public import AffineDominantTrace318
public section
noncomputable section
namespace FifthChartTrace318
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
local instance chartNonempty (b:Bool):Nonempty (chartOpen b):=chart_nonempty b
local instance chartNormal (b:Bool):IsIntegrallyClosed Γ(Target,chartOpen b):=chart_normal b
local instance preimageNonempty (b:Bool):Nonempty (map⁻¹ᵁchartOpen b):=
  DominantFunctionField318.preimage_nonempty map (chartOpen b)
lemma generic_finite:
    letI:=AffineDominantNorm318.fieldAlgebra map
    FiniteDimensional Target.functionField Model.functionField:=by
  letI:=AffineDominantNorm318.fieldAlgebra map
  apply Module.finite_of_finrank_pos
  rw [FifthCompletedDegree318.actual_generic_degree_eight]
  norm_num
/-- Genuine additive transfer of regular functions on both entire actual
target charts. The degree-eight generic scalar action is supplied explicitly. -/
@[expose] def trace (b:Bool):Γ(Model,map⁻¹ᵁchartOpen b)→+Γ(Target,chartOpen b):=
  AffineDominantTrace318.trace map (chartOpen b) (chart_affine b) generic_finite
lemma original_generic_trace (b:Bool) (s:Γ(Model,map⁻¹ᵁchartOpen b)):
    Target.germToFunctionField (chartOpen b) (trace b s)=
      FifthGenericTrace318.trace (Model.germToFunctionField (map⁻¹ᵁchartOpen b) s):=
  AffineDominantTrace318.embedding map (chartOpen b) (chart_affine b) generic_finite s
lemma trace_pullback (b:Bool) (s:Γ(Target,chartOpen b)):
    trace b (map.app (chartOpen b) s)=8*s:=by
  have h:=AffineDominantTrace318.pullback map (chartOpen b) (chart_affine b) generic_finite s
  simpa only [trace,FifthCompletedDegree318.actual_generic_degree_eight,nsmul_eq_mul,Nat.cast_ofNat] using h
lemma linearity (b:Bool) (a:Γ(Target,chartOpen b)) (s:Γ(Model,map⁻¹ᵁchartOpen b)):
    trace b (map.app (chartOpen b) a*s)=a*trace b s:=
  AffineDominantTrace318.linearity map (chartOpen b) (chart_affine b) generic_finite a s
/-- Vanishing at the actual source generic stalk is enough for this regular
trace to vanish as a whole target section, by the actual germ injection. -/
lemma zero_of_generic_trace (b:Bool) (s:Γ(Model,map⁻¹ᵁchartOpen b))
    (h:FifthGenericTrace318.trace (Model.germToFunctionField (map⁻¹ᵁchartOpen b) s)=0):
    trace b s=0:=by
  apply Target.germToFunctionField_injective (chartOpen b)
  rw [original_generic_trace,h,map_zero]
end FifthChartTrace318
