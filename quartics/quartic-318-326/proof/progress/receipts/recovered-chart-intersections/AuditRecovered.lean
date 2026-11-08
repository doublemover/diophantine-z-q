module
import all GenericOpenPushout318
import all WeierstrassChartPullback318
import all CompletedAdditionCharts318
import all WholeBothNaturality318
import all ChartInputEquality318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`GenericOpenPushout318,`WeierstrassChartPullback318,`CompletedAdditionCharts318,`WholeBothNaturality318,`ChartInputEquality318]
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == names.size do throwError "Missing module"
  logInfo m!"RECOVERED_INTERSECTION_AUDIT_PASS declarations={checked} modules={found}"
