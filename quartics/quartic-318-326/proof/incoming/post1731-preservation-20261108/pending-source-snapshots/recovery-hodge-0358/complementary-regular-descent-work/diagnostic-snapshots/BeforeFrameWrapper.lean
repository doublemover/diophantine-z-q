module
public import BranchGlobalDifferentialRestriction318
public import CharacterBranchActualRestriction318
public import IntrinsicChartLocalMultiple318
public import FrameUnitMultiple318
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
/-- Whole-ring coordinate divisibility and the specified normalized local
coefficient produce a regular multiple, retaining the exact inferred objects. -/
@[expose] def form_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):=
  FrameUnitMultiple318.of_factorization (ContactDifferentialFrames318.sourceLocalizationFrame units i)
    (BranchDifferentialDivisibility318.t units i) (CharacterBranchLocalForm318.unitCoefficient i i)
    (form i s) (CharacterBranchLocalForm318.form i i)
    (KaehlerDifferential.D ℚ (BranchDifferentialDivisibility318.B units i)
      (BranchDifferentialDivisibility318.t units i))
    (CharacterBranchLocalForm318.unitCoefficient_unit i i)
    (BranchDifferentialDivisibility318.coordinate_normalized units i)
    (invariant_factorization i s h) (CharacterBranchLocalForm318.omitted_frame_value i)
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE form_multiple"
  out.flush
/-- Actual entire-chart regular scalar multiple of the specified global
invariant, using its original whole-chart restriction. -/
@[expose] def section_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):=
  IntrinsicChartLocalMultiple318.section_multiple (X:=X) (R:=ℚ) (S:=B i)
    p (j i) (ContactIntrinsicFrames318.branch_structure units i)
    s (ContactCharacterDifferentials318.differential i) (CharacterBranchLocalForm318.form i i)
    (CharacterBranchActualRestriction318.restrict i i).symm (form_multiple i s h)
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE section_multiple"
  out.flush
end CharacterOmittedBranchMultiple318
