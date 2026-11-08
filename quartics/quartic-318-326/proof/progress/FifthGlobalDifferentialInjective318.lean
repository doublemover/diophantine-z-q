module
public import IntrinsicGlobalInvariantGenerator318
public import FifthGlobalScalarInjections318
public import FifthTargetDifferentialInvariants318
public import IntrinsicDifferentialGlobalScalars318
public section
noncomputable section
namespace FifthGlobalDifferentialInjective318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open FifthTargetDifferentialInvariants318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma pullback_smul (a:Γ(FifthCompletedGlobal318.Target,⊤)) (s:Γ(N,⊤)):
    pullback (a • s)=FifthCompletedGlobal318.map.appTop a • pullback s:=
  IntrinsicDifferentialGlobalScalars318.globalSection_smul FifthCompletedGlobal318.map p q
    FifthCompletedGlobal318.over_Q a s
/-- The canonical global intrinsic differential pullback of the actual fifth
quotient is injective. The proof retains the genuine target invariant frame,
actual scalar pullback and actual source form, not a dimension count. -/
theorem injective:Function.Injective pullback:=by
  intro s t h
  obtain ⟨a,rfl⟩:=(IntrinsicGlobalInvariantGenerator318.bijective A B discriminant_unit).surjective s
  obtain ⟨b,rfl⟩:=(IntrinsicGlobalInvariantGenerator318.bijective A B discriminant_unit).surjective t
  apply congrArg (fun a:Γ(FifthCompletedGlobal318.Target,⊤)=>a • IntrinsicGlobalFrame318.invariant A B discriminant_unit)
  apply FifthGlobalScalarInjections318.scalar_pullback_injective
  apply FifthGlobalScalarInjections318.multiply_injective
  exact (pullback_smul a (show Γ(N,⊤) from FifthActualDifferential318.invariant)).symm.trans
    (h.trans (pullback_smul b (show Γ(N,⊤) from FifthActualDifferential318.invariant)))
end FifthGlobalDifferentialInjective318
