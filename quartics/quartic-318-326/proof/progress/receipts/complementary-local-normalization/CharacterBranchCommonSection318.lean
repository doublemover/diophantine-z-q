module
public import CharacterBranchLocalForm318
public import CharacterCanonicalCommonRestriction318
public import BranchSectionExtension318
public section
noncomputable section
namespace CharacterBranchCommonSection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Exact actual common section equality, with canonical ambient and
literal ring presentations retained in all parameters. -/
@[expose] def equality (i j:Fin 4) :=
  (congrArg (IntrinsicChartSections318.sectionMap
    (Y:=ContactGlobalSmooth318.Model units) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder units)
    (ContactOverlapIntrinsic318.embedding units) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactOverlapIntrinsic318.over_Q units)) (CharacterBranchLocalForm318.common_eq i j)).trans
      (CharacterCanonicalCommonRestriction318.restrict i)
end CharacterBranchCommonSection318
