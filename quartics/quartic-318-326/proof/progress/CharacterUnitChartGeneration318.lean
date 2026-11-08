module
public import CharacterBranchActualRestriction318
public import CharacterInfinityActualRestriction318
public import IntrinsicChartScalarGeneration318
public section
noncomputable section
namespace CharacterUnitChartGeneration318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X:=ContactGlobalSmooth318.Model units
abbrev M:X.Modules:=ContactIntrinsicDifferentials318.omega units
/-- Any regular global section is a regular multiple of the chosen pulled
invariant on every nonomitted finite branch. -/
theorem branch_multiple (i j:Fin 4) (hij:i≠j) (s:Γ(M,⊤)):
    ∃a:Γ(X,ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤),
      M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤≤⊤ from le_top)).op s=
      a • M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤≤⊤ from le_top)).op
        (ContactCharacterDifferentials318.differential i):=by
  obtain ⟨a,ha⟩:=IntrinsicChartScalarGeneration318.surjective (X:=X) (R:=ℚ)
    (S:=ContactIntrinsicFrames318.BranchRing units j)
    (ContactIntrinsicFrames318.branchEmbedding units j) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactIntrinsicFrames318.branch_structure units j) (ContactDifferentialFrames318.sourceLocalizationFrame units j)
    (CharacterBranchLocalForm318.form i j) (CharacterBranchLocalForm318.frame_unit i j hij)
    (M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤≤⊤ from le_top)).op s)
  refine ⟨a,?_⟩
  exact ha.symm.trans (congrArg
    (fun t:Γ(M,ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤)=>a • t)
      (CharacterBranchActualRestriction318.restrict i j).symm)
/-- All four complementary invariants generate on the whole infinity
chart, so no invariant-form divisibility is needed at infinity here. -/
theorem infinity_multiple (i:Fin 4) (s:Γ(M,⊤)):
    ∃a:Γ(X,InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤),
      M.presheaf.map (homOfLE (show InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤≤⊤ from le_top)).op s=
      a • M.presheaf.map (homOfLE (show InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤≤⊤ from le_top)).op
        (ContactCharacterDifferentials318.differential i):=by
  have hw:IsUnit (ContactDifferentialFrames318.infinityFrame units (CharacterInfinityLocalForm318.form i)):=by
    rw [CharacterInfinityLocalForm318.frame_value]
    exact CharacterInfinityLocalForm318.coefficient_unit i
  obtain ⟨a,ha⟩:=IntrinsicChartScalarGeneration318.surjective (X:=X) (R:=ℚ)
    (S:=InfinityOpenChart318.OpenOrder units)
    (InfinityGlobalScheme318.chartEmbedding units) (ContactIntrinsicDifferentials318.structureMap units)
    (InfinityStructureSmooth318.chartEmbedding_over_Q units) (ContactDifferentialFrames318.infinityFrame units)
    (CharacterInfinityLocalForm318.form i) hw
    (M.presheaf.map (homOfLE (show InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤≤⊤ from le_top)).op s)
  refine ⟨a,?_⟩
  exact ha.symm.trans (congrArg
    (fun t:Γ(M,InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤)=>a • t)
      (CharacterInfinityActualRestriction318.restrict i).symm)
end CharacterUnitChartGeneration318
