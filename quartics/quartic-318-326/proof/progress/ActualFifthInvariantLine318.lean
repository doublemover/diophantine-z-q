module
public import FifthGlobalDifferentialDescent318
public import FifthGlobalDifferentialInjective318
public import ActualQuotientConstantPullback318
public section
noncomputable section
namespace ActualFifthInvariantLine318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthTargetDifferentialInvariants318
open ActualTargetRationalInvariants318 ActualQuotientConstantPullback318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- The same original structural rational constants, multiplying the
actual fifth source pullback with its established normalization. -/
@[expose] def parameter (a:ℚ):Γ(M,⊤):=
  sourceConstant a • FifthActualDifferential318.differential
lemma pullback_parameter (a:ℚ):
    pullback (fifthConstant a • FifthActualDifferential318.invariant)=parameter a:=
  fifth_invariant_multiple a
lemma parameter_injective:Function.Injective parameter:=by
  intro a b h
  apply fifth_bijective.injective
  apply FifthGlobalDifferentialInjective318.injective
  exact (pullback_parameter a).trans (h.trans (pullback_parameter b).symm)
/-- The actual fifth fixing-kernel invariant subspace is precisely the
unique structural rational multiples of the actual fifth pulled invariant. -/
theorem fixed_iff_existsUnique (s:Γ(M,⊤)):
    FifthDifferentialInvariantSummand318.Fixed s ↔ ∃!a:ℚ,parameter a=s:=by
  constructor
  · intro hs
    obtain ⟨t,ht⟩:=FifthGlobalDifferentialDescent318.exists_pullback s hs
    obtain ⟨a,ha⟩:=fifth_bijective.surjective t
    have he:parameter a=s:=
      (pullback_parameter a).symm.trans ((congrArg pullback ha).trans ht)
    exact ⟨a,he,fun b hb=>parameter_injective (hb.trans he.symm)⟩
  · rintro ⟨a,ha,_⟩
    rw [←ha,←pullback_parameter]
    exact FifthTargetDifferentialInvariants318.fixed _
theorem range_parameter:
    Set.range parameter={s:Γ(M,⊤)|FifthDifferentialInvariantSummand318.Fixed s}:=by
  ext s
  constructor
  · rintro ⟨a,ha⟩
    exact (fixed_iff_existsUnique s).mpr ⟨a,ha,fun b hb=>parameter_injective (hb.trans ha.symm)⟩
  · intro hs
    obtain ⟨a,ha,_⟩:=(fixed_iff_existsUnique s).mp hs
    exact ⟨a,ha⟩
end ActualFifthInvariantLine318
