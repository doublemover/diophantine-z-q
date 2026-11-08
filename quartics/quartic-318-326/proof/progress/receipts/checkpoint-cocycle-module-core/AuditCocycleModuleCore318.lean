module
import all CocycleModule318
import all CocycleModuleCone318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CocycleModule318, `CocycleModuleCone318]
  for n in #[`CocycleModule318.object, `CocycleModule318.compatible,
      `CocycleModule318.lift, `CocycleModule318.lift_coefficient,
      `CocycleModule318.hom_ext, `CocycleModuleCone318.isLimit,
      `CocycleModuleCone318.restrictedIsLimit] do
    unless env.contains n do throwError "Required endpoint missing: {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing target module"
  logInfo m!"COCYCLE_MODULE_CORE_AUDIT_PASS declarations={count} modules={found}"
