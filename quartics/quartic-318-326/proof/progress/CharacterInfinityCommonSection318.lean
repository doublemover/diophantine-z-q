module
public import CharacterInfinityLocalForm318
public import CharacterCanonicalCommonRestriction318
public import InfinityChartSectionExtension318
public section
noncomputable section
namespace CharacterInfinityCommonSection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Exact full-common-open equality of the infinity expression with the
original global complementary invariant pullback. -/
@[expose] def equality (i:Fin 4) :=
  (congrArg (IntrinsicChartSections318.sectionMap
    (Y:=ContactGlobalSmooth318.Model units) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder units)
    (ContactOverlapIntrinsic318.embedding units) (ContactIntrinsicDifferentials318.structureMap units)
    (ContactOverlapIntrinsic318.over_Q units)) (CharacterInfinityLocalForm318.common_eq i)).trans
      (CharacterCanonicalCommonRestriction318.restrict i)
end CharacterInfinityCommonSection318
