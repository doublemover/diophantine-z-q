module
public import FifthBranchCommonSection318
public import FifthCanonicalCommonRestriction318
public section
noncomputable section
namespace FifthBranchCommonGlobal318
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
/-- Exact common-open identity with the specified actual global pullback. -/
@[expose] def equality (j:Fin 4) :=
  (FifthBranchCommonSection318.equality j).trans FifthCanonicalCommonRestriction318.restrict
end FifthBranchCommonGlobal318
