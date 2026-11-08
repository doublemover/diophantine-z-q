module
public import IntrinsicGlobalInvariantGenerator318
public import CharacterGlobalScalarInjections318
public import CharacterTargetDifferentialInvariants318
public import IntrinsicDifferentialGlobalScalars318
public section
noncomputable section
namespace CharacterGlobalDifferentialInjective318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterTargetDifferentialInvariants318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma pullback_smul (i:Fin 4) (a:Γ(CompletedCharacterSchemeMaps318.Target i,⊤)) (s:Γ(N i,⊤)):
    pullback i (a • s)=(CompletedCharacterGlobal318.completedMap i).appTop a • pullback i s:=
  IntrinsicDifferentialGlobalScalars318.globalSection_smul (CompletedCharacterGlobal318.completedMap i) p (q i)
    (CompletedCharacterGlobal318.over_Q i) a s
/-- Injectivity of the original canonical global Omega pullback of each
actual complementary quotient, using its specified target invariant frame. -/
theorem injective (i:Fin 4):Function.Injective (pullback i):=by
  intro s t h
  obtain ⟨a,rfl⟩:=(IntrinsicGlobalInvariantGenerator318.bijective (publishedA i) (publishedB i)
    (ContactCharacterDifferentials318.discriminantUnit i)).surjective s
  obtain ⟨b,rfl⟩:=(IntrinsicGlobalInvariantGenerator318.bijective (publishedA i) (publishedB i)
    (ContactCharacterDifferentials318.discriminantUnit i)).surjective t
  apply congrArg (fun a:Γ(CompletedCharacterSchemeMaps318.Target i,⊤)=>a • ContactCharacterDifferentials318.invariant i)
  apply CharacterGlobalScalarInjections318.scalar_pullback_injective i
  apply CharacterGlobalScalarInjections318.multiply_injective i
  exact (pullback_smul i a (show Γ(N i,⊤) from ContactCharacterDifferentials318.invariant i)).symm.trans
    (h.trans (pullback_smul i b (show Γ(N i,⊤) from ContactCharacterDifferentials318.invariant i)))
end CharacterGlobalDifferentialInjective318
