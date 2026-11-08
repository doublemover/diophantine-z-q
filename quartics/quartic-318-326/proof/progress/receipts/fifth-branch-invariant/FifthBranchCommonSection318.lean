module
public import BranchSectionExtension318
public section
noncomputable section
namespace FifthBranchCommonSection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- The exact algebraic common-open equality as sections, with the actual
canonical Scheme and algebra presentations fixed in every parameter. -/
@[expose] def equality (j:Fin 4) :=
  congrArg (IntrinsicChartSections318.sectionMap
    (Y:=ContactGlobalSmooth318.Model units) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder units)
    (ContactOverlapIntrinsic318.embedding units) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactOverlapIntrinsic318.over_Q units)) (FifthBranchDifferential318.common_eq j)
end FifthBranchCommonSection318
