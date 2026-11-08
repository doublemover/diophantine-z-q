module
import all FifthBranchEquation318
import all FifthBranchLocal318
import all FifthBranchScheme318
import all FifthBranchOverlap318
import all FifthBranchAgreement318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthBranchEquation318,`FifthBranchLocal318,`FifthBranchScheme318,`FifthBranchOverlap318,`FifthBranchAgreement318]
  for name in #[`FifthBranchEquation318.regular_equation,`FifthBranchLocal318.infinityMap,`FifthBranchLocal318.origin_composition,`FifthBranchScheme318.branch_zero,`FifthBranchScheme318.branchLift_inclusion,`FifthBranchScheme318.over_Q,`FifthBranchAgreement318.chart_agreement,`FifthBranchAgreement318.agreement] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 5 do throwError "Expected five modules, found {found}"
  logInfo m!"FIFTH_BRANCH_EXTENSION_AUDIT_PASS declarations={checked} modules={found}"
