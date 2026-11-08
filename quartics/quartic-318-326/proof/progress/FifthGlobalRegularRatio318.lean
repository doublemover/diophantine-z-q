module
public import GlobalScalarMultipleGluing318
public import IntrinsicChartScalarGeneration318
public import FifthCommonScalarInjection318
public import FifthInfinityRegularMultiple318
public import FifthBranchInvariantRestriction318
public section
noncomputable section
namespace FifthGlobalRegularRatio318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev X:=ContactGlobalSmooth318.Model units
abbrev M:=ContactIntrinsicDifferentials318.omega units
local instance modelIntegral:IsIntegral X:=
  (ContactGlobalSmooth318.smooth_proper_integral_model units).2.2
lemma branch_multiple (s:Γ(M,⊤)) (i:Fin 4):
    ∃a:Γ(X,ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤),
      M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤≤⊤ from le_top)).op s=
      a • M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤≤⊤ from le_top)).op
        FifthActualDifferential318.differential:=by
  have hw:IsUnit (ContactDifferentialFrames318.sourceLocalizationFrame units i
      (FifthBranchDifferential318.form i)):=by
    rw [FifthBranchDifferential318.frame_value]
    exact FifthBranchUnitCoefficient318.coefficient_unit i
  obtain ⟨a,ha⟩:=IntrinsicChartScalarGeneration318.surjective (X:=X) (R:=ℚ)
    (S:=ContactIntrinsicFrames318.BranchRing units i)
    (ContactIntrinsicFrames318.branchEmbedding units i) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactIntrinsicFrames318.branch_structure units i)
    (ContactDifferentialFrames318.sourceLocalizationFrame units i)
    (FifthBranchDifferential318.form i) hw
    (M.presheaf.map (homOfLE (show ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤≤⊤ from le_top)).op s)
  refine ⟨a,?_⟩
  exact ha.symm.trans (congrArg (fun t:Γ(M,ContactIntrinsicFrames318.branchEmbedding units i ''ᵁ ⊤)=>a • t)
    (FifthBranchInvariantRestriction318.restrict i).symm)
lemma local_multiple (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s)
    (i:Option (Fin 4)):
    ∃a:Γ(X,ContactGlobalBicanonical318.opens units i),
      M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units i≤⊤ from le_top)).op s=
      a • M.presheaf.map (homOfLE (show ContactGlobalBicanonical318.opens units i≤⊤ from le_top)).op
        FifthActualDifferential318.differential:=by
  cases i with
  | none =>
      obtain ⟨a,ha⟩:=FifthInfinityRegularMultiple318.section_multiple s h
      exact ⟨ScaledGlobalSectionRestriction318.scalar (InfinityGlobalScheme318.chartEmbedding units) a,ha⟩
  | some i => exact branch_multiple s i
/-- Every actual eight-sign invariant global intrinsic differential is a
regular global source function times the actual fifth invariant pullback.
The scalar is glued on the entire five-chart cover, including all branch
points and the infinity divisor. -/
theorem exists_global_ratio (s:Γ(M,⊤)) (h:FifthDifferentialInvariantSummand318.Fixed s):
    ∃r:Γ(X,⊤),s=r • FifthActualDifferential318.differential:=by
  choose a ha using local_multiple s h
  exact GlobalScalarMultipleGluing318.exists_global M
    (ContactGlobalBicanonical318.opens units) (ContactGlobalBicanonical318.cover units)
    (ContactGlobalSectionDetection318.common units) (ContactGlobalSectionDetection318.common_le units)
    s FifthActualDifferential318.differential FifthCommonScalarInjection318.injective a ha
/-- In particular the actual averaging operator has a globally regular
source ratio; this is not yet a target regular differential descent theorem. -/
theorem average_global_ratio (s:Γ(M,⊤)):
    ∃r:Γ(X,⊤),FifthDifferentialAveraging318.average s=r • FifthActualDifferential318.differential:=
  exists_global_ratio _ (FifthDifferentialInvariantSummand318.average_fixed s)
end FifthGlobalRegularRatio318
