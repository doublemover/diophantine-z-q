module
public import CharacterBranchLocalForm318
public section
noncomputable section
namespace CharacterBranchVectorFactorization318
open SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev B (i:Fin 4):=ContactIntrinsicFrames318.BranchRing units i
lemma root_coordinate (i:Fin 4):CharacterBranchLocalForm318.root i i=
    ContactFrameNormalization318.sourceCoordinate units i:=
  (BranchOriginalCoordinate318.coordinate_eq_root units i).symm
/-- The specified local differential has the exact unit-times-coordinate
factorization by its literal definition, without a second frame conversion. -/
theorem factorization (i:Fin 4):CharacterBranchLocalForm318.form i i=
    (CharacterBranchLocalForm318.unitCoefficient i i*ContactFrameNormalization318.sourceCoordinate units i) •
      KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i):=by
  rw [CharacterBranchLocalForm318.form,FifthBranchDifferential318.form,smul_smul]
  apply congrArg (fun a:B i=>a • KaehlerDifferential.D ℚ (B i)
    (ContactFrameNormalization318.sourceCoordinate units i))
  rw [root_coordinate]
  unfold CharacterBranchLocalForm318.unitCoefficient
  ring
end CharacterBranchVectorFactorization318
