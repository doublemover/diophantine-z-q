module
public import FifthRegularDifferentialDescent318
public import FifthTargetDifferentialInvariants318
public import IntrinsicDifferentialGlobalScalars318
public section
noncomputable section
namespace FifthGlobalDifferentialDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthTargetDifferentialInvariants318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Actual regular target differentials, rather than rational coefficients,
account for every eight-sign invariant intrinsic global source section. -/
theorem exists_pullback (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃t:Γ(N,⊤),pullback t=s:=by
  obtain ⟨g,hg⟩:=FifthRegularDifferentialDescent318.exists_target_multiple s h
  refine ⟨g • FifthActualDifferential318.invariant,?_⟩
  change IntrinsicDifferentialPullback318.globalSection FifthCompletedGlobal318.map p q
    FifthCompletedGlobal318.over_Q (g • FifthActualDifferential318.invariant)=s
  exact (IntrinsicDifferentialGlobalScalars318.globalSection_smul FifthCompletedGlobal318.map p q
    FifthCompletedGlobal318.over_Q g FifthActualDifferential318.invariant).trans hg.symm
/-- Exact range of the original completed quotient's canonical pullback on
regular global intrinsic Omega. No sheaf-level trace or Picard map is asserted. -/
theorem range_pullback:Set.range pullback={s:Γ(M,⊤)|FifthDifferentialInvariantSummand318.Fixed s}:=by
  ext s
  constructor
  · rintro ⟨t,rfl⟩;exact FifthTargetDifferentialInvariants318.fixed t
  · exact exists_pullback s
/-- The previously constructed actual global averaging summand is exactly
the range of pullback from regular target global differentials. -/
theorem range_average_eq_range_pullback:
    Set.range FifthDifferentialAveraging318.average=Set.range pullback:=by
  rw [range_pullback,FifthDifferentialInvariantSummand318.range_average]
theorem average_descends (s:Γ(M,⊤)):
    ∃t:Γ(N,⊤),pullback t=FifthDifferentialAveraging318.average s:=
  exists_pullback _ (FifthDifferentialInvariantSummand318.average_fixed s)
end FifthGlobalDifferentialDescent318
