module
public import FifthDifferentialTraceComparison318
public import ContactGlobalCoefficientScalars318
public section
noncomputable section
namespace FifthDifferentialProjection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318
open ContactGlobalDifferentialCoefficient318 FifthDifferentialTraceComparison318
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
/-- The normalized actual differential average has the genuine normalized
field trace as its dt coefficient in the actual target generic stalk. -/
theorem coefficient_average (s:Γ(FifthSignRestriction318.M,⊤)):
    coefficient (FifthDifferentialAveraging318.average s)=
      (targetEquiv (FifthTraceProjection318.retraction (genericCoefficient s)):Raw):=by
  rw [FifthDifferentialAveraging318.average,ContactGlobalCoefficientScalars318.coefficient_smul,
    coefficient_signSum_trace,FifthTraceProjection318.retraction_apply]
  simp only [map_mul,map_inv₀,map_ofNat,one_div]
  rw [IntermediateField.coe_mul,IntermediateField.coe_inv]
  rfl
/-- Before any presentation of the function fields, normalized averaging
is exactly the actual pullback-after-trace projection on dt coefficients. -/
theorem generic_average (s:Γ(FifthSignRestriction318.M,⊤)):
    genericCoefficient (FifthDifferentialAveraging318.average s)=
      FifthTraceProjection318.projection (genericCoefficient s):=by
  apply sourceEquiv.injective
  rw [genericCoefficient_raw,coefficient_average,FifthTraceProjection318.projection]
  exact (DFunLike.congr_fun FifthCompletedDegree318.actual_field_square _).symm
/-- Idempotence on every actual global intrinsic differential follows from
its genuine generic trace comparison and the proved whole-open detection.
This does not assert that its image is all pullbacks of regular target forms. -/
theorem average_twice (s:Γ(FifthSignRestriction318.M,⊤)):
    FifthDifferentialAveraging318.average (FifthDifferentialAveraging318.average s)=
      FifthDifferentialAveraging318.average s:=by
  apply ContactGlobalCoefficientScalars318.coefficient_injective
  have h:genericCoefficient (FifthDifferentialAveraging318.average (FifthDifferentialAveraging318.average s))=
      genericCoefficient (FifthDifferentialAveraging318.average s):=by
    rw [generic_average,generic_average,FifthTraceProjection318.projection_twice]
  simpa only [genericCoefficient_raw] using congrArg sourceEquiv h
end FifthDifferentialProjection318
