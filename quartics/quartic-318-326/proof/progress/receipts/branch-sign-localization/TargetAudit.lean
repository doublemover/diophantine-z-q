module
import all BranchSignLocalization318
import all BranchSignScheme318
import all BranchFlipQuotient318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`BranchSignLocalization318,`BranchSignScheme318,`BranchFlipQuotient318]
  for name in #[`BranchSignLocalization318.on_source,`BranchSignLocalization318.flip_coordinate,
      `BranchSignLocalization318.flip_other_root,`BranchSignScheme318.actual_square,
      `BranchSignScheme318.flip_square,`BranchFlipQuotient318.quotient_fixed,
      `BranchFlipQuotient318.divisible] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Endpoint not proposition: {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==3 do throwError "Expected three modules, found {found}"
  logInfo m!"BRANCH_SIGN_AUDIT_PASS declarations={n} modules={found}"
