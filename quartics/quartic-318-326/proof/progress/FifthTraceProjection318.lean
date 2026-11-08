module
public import FifthGenericTrace318
public section
noncomputable section
namespace FifthTraceProjection318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthCompletedFunctionField318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
local instance characterCharZero:CharZero Character:=Algebra.charZero_of_charZero (RatFunc ℚ) Character
local instance targetCharZero:CharZero Target.functionField:=targetEquiv.toRingHom.charZero
/-- Division by the genuine degree gives a linear retraction of the actual
completed quotient's function-field pullback. -/
@[expose] def retraction:Model.functionField→ₗ[Target.functionField]Target.functionField:=
  (8:Target.functionField)⁻¹ • FifthGenericTrace318.trace
lemma retraction_apply (x:Model.functionField):retraction x=(8:Target.functionField)⁻¹*FifthGenericTrace318.trace x:=rfl
@[simp] lemma retraction_pullback (x:Target.functionField):
    retraction (FifthCompletedDegree318.pullback x)=x:=by
  rw [retraction_apply,FifthGenericTrace318.trace_pullback]
  field_simp
/-- The associated actual pullback-after-transfer idempotent. It projects
onto the original fifth subfield; it is not an isomorphism of the source. -/
@[expose] def projection (x:Model.functionField):Model.functionField:=
  FifthCompletedDegree318.pullback (retraction x)
@[simp] lemma projection_pullback (x:Target.functionField):
    projection (FifthCompletedDegree318.pullback x)=FifthCompletedDegree318.pullback x:=by
  rw [projection,retraction_pullback]
@[simp] lemma projection_twice (x:Model.functionField):projection (projection x)=projection x:=by
  exact projection_pullback (retraction x)
lemma projection_range: Set.range projection=Set.range FifthCompletedDegree318.pullback:=by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨retraction y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact ⟨FifthCompletedDegree318.pullback y,projection_pullback y⟩
lemma retraction_surjective:Function.Surjective retraction:=by
  intro x
  exact ⟨FifthCompletedDegree318.pullback x,retraction_pullback x⟩
end FifthTraceProjection318
