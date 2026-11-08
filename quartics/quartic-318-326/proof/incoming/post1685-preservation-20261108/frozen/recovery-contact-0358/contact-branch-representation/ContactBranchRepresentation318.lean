module
public import IntrinsicChartRepresentation318
public import BranchSignScheme318
public section
noncomputable section
namespace ContactBranchRepresentation318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev X:=ContactGlobalSmooth318.Model c
abbrev B (i:Fin 4):=ContactIntrinsicFrames318.BranchRing c i
abbrev p:X c⟶Spec (CommRingCat.of ℚ):=ContactIntrinsicDifferentials318.structureMap c
abbrev j (i:Fin 4):Spec (CommRingCat.of (B c i))⟶X c:=ContactIntrinsicFrames318.branchEmbedding c i
abbrev M:(X c).Modules:=FamilyIntrinsicDifferentials318.omega (p c)
/-- Canonical whole-branch representative, with the twist family kept
abstract rather than normalizing a fixed tuple inside the localization. -/
@[expose] def representation (i:Fin 4):=
  IntrinsicChartRepresentation318.representation (X:=X c) (R:=ℚ) (S:=B c i)
    (p c) (j c i) (ContactIntrinsicFrames318.branch_structure c i)
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE branch representation"
  out.flush
/-- Exact actual chart restriction of the canonical algebraic representative. -/
@[expose] def representation_restrict (i:Fin 4) (s:Γ(M c,⊤)):=
  IntrinsicChartRepresentation318.representation_restrict (X:=X c) (R:=ℚ) (S:=B c i)
    (p c) (j c i) (ContactIntrinsicFrames318.branch_structure c i) s
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE branch restriction"
  out.flush
/-- Every specified original root sign acts through its actual whole-branch
algebra map. The actual base-square proof is an explicit input. -/
@[expose] def representation_action (i:Fin 4) (b:Fin 4→Bool)
    (hf:ContactGlobalSigns318.map c b≫p c=p c) (s:Γ(M c,⊤)):=
  IntrinsicChartRepresentation318.representation_action (X:=X c) (R:=ℚ) (S:=B c i)
    (p c) (j c i) (ContactIntrinsicFrames318.branch_structure c i)
    (ContactGlobalSigns318.map c b) hf (BranchSignLocalization318.sign c i b).toAlgHom
    (BranchSignScheme318.actual_square c i b).symm s
run_cmd do
  let out ← IO.getStdout
  out.putStrLn "DONE branch action"
  out.flush
end ContactBranchRepresentation318
