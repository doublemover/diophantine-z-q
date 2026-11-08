module
public import FifthBranchCommonSection318
public import FifthCanonicalCommonRestriction318
public section
noncomputable section
namespace FifthBranchInvariantRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthBranchUnitCoefficient318
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev M:=ContactIntrinsicDifferentials318.omega units
/-- The actual fifth completed-map invariant pulls back on each entire
finite branch chart to the exact unit coefficient times its original-root
universal differential. No punctured-chart equality is used as the endpoint. -/
@[expose] def restrict (j:Fin 4) :=
  BranchSectionExtension318.section_eq units j FifthActualDifferential318.differential
    (FifthBranchDifferential318.form j)
    ((FifthBranchCommonSection318.equality j).trans FifthCanonicalCommonRestriction318.restrict)
/-- Every branch is included. This inferred proposition retains the exact
chosen chart/sheaf structures and the explicit coefficient via form. -/
@[expose] def unit_frame_and_restrict (j:Fin 4) :=
  And.intro (coefficient_unit j) (restrict j)
end FifthBranchInvariantRestriction318
