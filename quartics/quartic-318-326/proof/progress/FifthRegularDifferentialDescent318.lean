module
public import FifthGlobalRegularRatio318
public import FifthInvariantRatioField318
public import FifthRegularScalarDescent318
public section
noncomputable section
namespace FifthRegularDifferentialDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthCompletedGlobal318 FifthCompletedFunctionField318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Every actual eight-sign invariant intrinsic global differential is a
regular target function pulled back along the actual fifth quotient times
its actual pulled elliptic invariant differential. -/
theorem exists_target_multiple (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃g:Γ(Target,⊤),s=FifthCompletedGlobal318.map.appTop g • FifthActualDifferential318.differential:=by
  obtain ⟨r,hr⟩:=FifthGlobalRegularRatio318.exists_global_ratio s h
  obtain ⟨g,hg⟩:=FifthRegularScalarDescent318.exists_target r
    (FifthInvariantRatioField318.ratio_range s h r hr)
  exact ⟨g,hg.symm ▸ hr⟩
theorem average_target_multiple (s:Γ(M,⊤)):
    ∃g:Γ(Target,⊤),FifthDifferentialAveraging318.average s=
      FifthCompletedGlobal318.map.appTop g • FifthActualDifferential318.differential:=
  exists_target_multiple _ (FifthDifferentialInvariantSummand318.average_fixed s)
end FifthRegularDifferentialDescent318
