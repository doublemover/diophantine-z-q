module
public import CharacterOmittedBranchMultiple318
public import CharacterUnitChartGeneration318
public import CharacterCommonScalarInjection318
public import GlobalScalarMultipleGluing318
public section
noncomputable section
namespace CharacterGlobalRegularRatio318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X:=ContactGlobalSmooth318.Model units
abbrev M:X.Modules:=ContactIntrinsicDifferentials318.omega units
local instance modelIntegral:IsIntegral X:=(ContactGlobalSmooth318.smooth_proper_integral_model units).2.2
lemma local_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s)
    (k:Option (Fin 4)):
    ∃a:Γ(X,ContactGlobalBicanonical318.opens units k),
      M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units k≤⊤ from le_top)).op s=
      a • M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units k≤⊤ from le_top)).op
        (ContactCharacterDifferentials318.differential i):=by
  cases k with
  | none=>exact CharacterUnitChartGeneration318.infinity_multiple i s
  | some j=>
      by_cases hij:i=j
      · subst j;exact CharacterOmittedBranchMultiple318.section_multiple i s h
      · exact CharacterUnitChartGeneration318.branch_multiple i j hij s
/-- Every genuine invariant global differential has a globally regular
source ratio on the full five-chart cover. Finite omitted-branch divisibility
and the whole-infinity unit frame are used in their correct distinct places. -/
theorem exists_global_ratio (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃r:Γ(X,⊤),s=r • ContactCharacterDifferentials318.differential i:=by
  choose a ha using local_multiple i s h
  exact GlobalScalarMultipleGluing318.exists_global M
    (ContactGlobalBicanonical318.opens units) (ContactGlobalBicanonical318.cover units)
    (ContactGlobalSectionDetection318.common units) (ContactGlobalSectionDetection318.common_le units)
    s (ContactCharacterDifferentials318.differential i) (CharacterCommonScalarInjection318.injective i) a ha
end CharacterGlobalRegularRatio318
