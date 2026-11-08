module
public import FifthCompletedDegree318
public import Mathlib.RingTheory.Trace.Basic
public section
noncomputable section
namespace FifthGenericTrace318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCharacterShortPolynomial318 FifthCompletedGlobal318 FifthCompletedFunctionField318
set_option maxHeartbeats 450000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral:IsIntegral Target:=FifthCompletedProper318.target_proper_integral.2
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
local instance characterAlgebra:Algebra Order Character:=FifthShortFraction318.embedding.toAlgebra
attribute [local instance] sourceAlgebra targetAlgebra FifthCompletedDegree318.pullbackAlgebra
local instance originalFinite:FiniteDimensional Character Raw:=
  Module.finite_of_finrank_pos (by rw [FifthCharacterField318.relative_degree_eight];norm_num)
local instance fullGalois:IsGalois (RatFunc ℚ) Raw:=ActualKummerGalois318.source_raw_galois units
local instance relativeGalois:IsGalois Character Raw:=inferInstance
local instance fixingFinite:Finite FifthCharacterField318.field.fixingSubgroup:=by
  apply Nat.finite_of_card_ne_zero
  rw [FifthCharacterField318.fixing_subgroup_card]
  decide
local instance fixingFintype:Fintype FifthCharacterField318.field.fixingSubgroup:=Fintype.ofFinite _
/-- The linear trace for the actual generic-stalk scalar action of the
completed fifth quotient, not an abstract extension assigned by its degree. -/
@[expose] def trace:Model.functionField→ₗ[Target.functionField]Target.functionField:=
  Algebra.trace Target.functionField Model.functionField
lemma trace_pullback (x:Target.functionField):trace (FifthCompletedDegree318.pullback x)=8*x:=by
  change Algebra.trace Target.functionField Model.functionField
    (algebraMap Target.functionField Model.functionField x)=_
  rw [Algebra.trace_algebraMap,FifthCompletedDegree318.actual_generic_degree_eight]
  simp only [nsmul_eq_mul,Nat.cast_ofNat]
/-- The exact source and target generic-stalk identifications compare traces. -/
lemma original_trace (x:Model.functionField):targetEquiv (trace x)=
    Algebra.trace Character Raw (sourceEquiv x):=by
  have hc:(algebraMap Character Raw).comp targetEquiv.toRingHom=
      sourceEquiv.toRingHom.comp (algebraMap Target.functionField Model.functionField):=
    FifthCompletedDegree318.actual_field_square.symm
  have h:=Algebra.trace_eq_of_equiv_equiv targetEquiv.toRingEquiv sourceEquiv.toRingEquiv hc x
  change targetEquiv (Algebra.trace Target.functionField Model.functionField x)=_
  rw [h]
  exact targetEquiv.apply_symm_apply _
/-- Exactly the eight genuine fixing automorphisms of the original full-root
character, with no arbitrary labels replacing the actual source action. -/
lemma original_trace_sum (x:Model.functionField):
    (targetEquiv (trace x):Raw)=
      ∑σ:FifthCharacterField318.field.fixingSubgroup,σ.1 (sourceEquiv x):=by
  rw [original_trace]
  calc
    _=∑σ:Raw≃ₐ[Character]Raw,σ (sourceEquiv x):=
      trace_eq_sum_automorphisms (K:=Character) (sourceEquiv x)
    _=_:= (Fintype.sum_equiv FifthCharacterField318.field.fixingSubgroupEquiv.toEquiv
      (fun σ=>σ.1 (sourceEquiv x)) (fun σ=>σ (sourceEquiv x)) (fun _=>rfl)).symm
lemma fixing_automorphisms_card:Nat.card FifthCharacterField318.field.fixingSubgroup=8:=
  FifthCharacterField318.fixing_subgroup_card
end FifthGenericTrace318
