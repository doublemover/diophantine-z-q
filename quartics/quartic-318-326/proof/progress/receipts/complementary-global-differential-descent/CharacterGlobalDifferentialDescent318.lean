module
public import CharacterRegularDifferentialDescent318
public import CharacterTargetDifferentialInvariants318
public import IntrinsicDifferentialGlobalScalars318
public section
noncomputable section
namespace CharacterGlobalDifferentialDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterTargetDifferentialInvariants318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Actual regular target global Omega accounts for every source section
fixed by the eight signs fixing the actual completed complementary map. -/
theorem exists_pullback (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃t:Γ(N i,⊤),pullback i t=s:=by
  obtain ⟨g,hg⟩:=CharacterRegularDifferentialDescent318.exists_target_multiple i s h
  refine ⟨g • ContactCharacterDifferentials318.invariant i,?_⟩
  change IntrinsicDifferentialPullback318.globalSection (CompletedCharacterGlobal318.completedMap i) p (q i)
    (CompletedCharacterGlobal318.over_Q i) (g • ContactCharacterDifferentials318.invariant i)=s
  exact (IntrinsicDifferentialGlobalScalars318.globalSection_smul (CompletedCharacterGlobal318.completedMap i) p (q i)
    (CompletedCharacterGlobal318.over_Q i) g (ContactCharacterDifferentials318.invariant i)).trans hg.symm
/-- Exact range of the original whole-Scheme canonical pullback on regular
global intrinsic differentials, separately for all four original quotients. -/
theorem range_pullback (i:Fin 4):
    Set.range (pullback i)={s:Γ(M,⊤)|CharacterDifferentialInvariants318.Fixed i s}:=by
  ext s
  constructor
  · rintro ⟨t,rfl⟩
    exact CharacterTargetDifferentialInvariants318.fixed i t
  · exact exists_pullback i s
end CharacterGlobalDifferentialDescent318
