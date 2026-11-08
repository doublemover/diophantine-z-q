module
public import ContactGlobalFunctionCoefficient318
public import FifthDifferentialInvariantSummand318
public import FiveActualPullbacksIndependent318
public section
noncomputable section
namespace FifthInvariantRatioField318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318 FifthDifferentialTraceComparison318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
local instance modelTop:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
abbrev M:=ContactIntrinsicDifferentials318.omega units
lemma coefficient_range (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    Set.range FifthCompletedDegree318.pullback (genericCoefficient s):=by
  refine ⟨FifthTraceProjection318.retraction (genericCoefficient s),?_⟩
  change FifthTraceProjection318.projection (genericCoefficient s)=genericCoefficient s
  rw [←FifthDifferentialProjection318.generic_average,
    FifthDifferentialInvariantSummand318.average_eq_of_fixed s h]
lemma fifth_fixed:FifthDifferentialInvariantSummand318.Fixed FifthActualDifferential318.differential:=
  (FifthDifferentialInvariantSummand318.average_eq_iff _).mp FifthDifferentialAveraging318.average_fifth
lemma fifth_coefficient_ne_zero:genericCoefficient FifthActualDifferential318.differential≠0:=by
  intro h
  apply FiveActualPullbacksIndependent318.fifth_nonzero
  apply ContactGlobalCoefficientScalars318.coefficient_injective
  have hh:=congrArg sourceEquiv h
  simpa only [genericCoefficient_raw,map_zero] using hh
/-- Dividing two invariant differential coefficients identifies the genuine
generic germ of their globally regular scalar ratio with the actual target
function-field image; it makes no regularity inference by itself. -/
theorem ratio_range (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s)
    (r:Γ(Model,⊤)) (hr:s=r • FifthActualDifferential318.differential):
    Set.range FifthCompletedDegree318.pullback (Model.germToFunctionField ⊤ r):=by
  obtain ⟨a,ha⟩:=coefficient_range FifthActualDifferential318.differential fifth_fixed
  obtain ⟨b,hb⟩:=coefficient_range s h
  refine ⟨b/a,?_⟩
  rw [map_div₀,ha,hb,hr,ContactGlobalFunctionCoefficient318.genericCoefficient_smul,
    mul_div_cancel_right₀ _ fifth_coefficient_ne_zero]
end FifthInvariantRatioField318
