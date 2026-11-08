module
public import CharacterInfinityCommonSection318
public section
noncomputable section
namespace CharacterInfinityActualRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Every original complementary pulled invariant has a unit coefficient
on the entire infinity chart, including every point of u=0. -/
@[expose] def restrict (i:Fin 4) :=
  InfinityChartSectionExtension318.section_eq units (ContactCharacterDifferentials318.differential i)
    (CharacterInfinityLocalForm318.form i) (CharacterInfinityCommonSection318.equality i)
end CharacterInfinityActualRestriction318
