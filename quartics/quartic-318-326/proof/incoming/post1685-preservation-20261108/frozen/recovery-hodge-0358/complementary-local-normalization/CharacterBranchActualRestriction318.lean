module
public import CharacterBranchCommonSection318
public section
noncomputable section
namespace CharacterBranchActualRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Every original complementary pulled invariant has its exact local
normalization on every entire finite branch, including its vanishing branch. -/
@[expose] def restrict (i j:Fin 4) :=
  BranchSectionExtension318.section_eq units j (ContactCharacterDifferentials318.differential i)
    (CharacterBranchLocalForm318.form i j) (CharacterBranchCommonSection318.equality i j)
end CharacterBranchActualRestriction318
