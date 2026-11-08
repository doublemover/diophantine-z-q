module
public import CharacterOmittedBranchAlgebra318
public import CharacterBranchActualRestriction318
public import IntrinsicChartLocalMultiple318
public import KaehlerModuleMultiple318
public section
noncomputable section
namespace CharacterOmittedBranchMultiple318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open BranchGlobalDifferentialRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Actual entire-chart regular scalar multiple of the specified global
invariant, using its original whole-chart restriction. -/
@[expose] def section_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s) :=
  IntrinsicChartLocalMultiple318.section_multiple (X:=ContactGlobalSmooth318.Model units) (R:=ℚ)
    (S:=ContactIntrinsicFrames318.BranchRing units i)
    (ContactIntrinsicDifferentials318.structureMap units) (ContactIntrinsicFrames318.branchEmbedding units i)
    (ContactIntrinsicFrames318.branch_structure units i)
    s (ContactCharacterDifferentials318.differential i) (CharacterBranchLocalForm318.form i i)
    (CharacterBranchActualRestriction318.restrict i i).symm
    (KaehlerModuleMultiple318.to_direct (R:=ℚ) (S:=B i) (form i s)
      (CharacterBranchLocalForm318.form i i) (CharacterOmittedBranchAlgebra318.form_multiple i s h))
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE section_multiple"
  out.flush
end CharacterOmittedBranchMultiple318
