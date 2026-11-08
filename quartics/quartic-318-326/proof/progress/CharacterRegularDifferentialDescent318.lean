module
public import CharacterGlobalRegularRatio318
public import CharacterInvariantRatioField318
public import CompletedCharacterRegularDescent318
public section
noncomputable section
namespace CharacterRegularDifferentialDescent318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- Every invariant regular source differential is the actual pullback of
an everywhere regular target function times the specified pulled invariant. -/
theorem exists_target_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃g:Γ(Target i,⊤),s=(completedMap i).appTop g • ContactCharacterDifferentials318.differential i:=by
  obtain ⟨r,hr⟩:=CharacterGlobalRegularRatio318.exists_global_ratio i s h
  obtain ⟨g,hg⟩:=CompletedCharacterRegularDescent318.exists_target i r
    (CharacterInvariantRatioField318.ratio_range i s h r hr)
  exact ⟨g,hg.symm ▸ hr⟩
end CharacterRegularDifferentialDescent318
