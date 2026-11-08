module
public import ContactGlobalDifferentialCoefficient318
public import FifthFixingFieldEnumeration318
public import FifthTraceProjection318
public section
noncomputable section
namespace FifthDifferentialTraceComparison318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318
open ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
/-- The actual generic-stalk function representing the whole-open dt
coefficient of a global source differential. -/
@[expose] def genericCoefficient (s:Γ(FifthSignRestriction318.M,⊤)):Model.functionField:=
  sourceEquiv.symm (coefficient s)
lemma genericCoefficient_raw (s:Γ(FifthSignRestriction318.M,⊤)):
    sourceEquiv (genericCoefficient s)=coefficient s:=sourceEquiv.apply_symm_apply _
/-- Actual source-global differential averaging matches the genuine field
trace on its dt coefficient. The right side is embedded from the actual
target generic stalk; this does not assert extension to target Omega. -/
theorem coefficient_signSum_trace (s:Γ(FifthSignRestriction318.M,⊤)):
    coefficient (FifthDifferentialAveraging318.signSum s)=
      (targetEquiv (FifthGenericTrace318.trace (genericCoefficient s)):Raw):=by
  rw [ContactGlobalDifferentialCoefficient318.coefficient_signSum,
    FifthFixingFieldEnumeration318.sum_eq,FifthGenericTrace318.original_trace_sum,
    genericCoefficient_raw]
/-- The same identity before selecting an original-field presentation. Its
right side retains the literal contravariant generic-stalk pullback. -/
theorem generic_signSum_trace (s:Γ(FifthSignRestriction318.M,⊤)):
    genericCoefficient (FifthDifferentialAveraging318.signSum s)=
      FifthCompletedDegree318.pullback (FifthGenericTrace318.trace (genericCoefficient s)):=by
  apply sourceEquiv.injective
  rw [genericCoefficient_raw,coefficient_signSum_trace]
  exact (DFunLike.congr_fun FifthCompletedDegree318.actual_field_square _).symm
end FifthDifferentialTraceComparison318
