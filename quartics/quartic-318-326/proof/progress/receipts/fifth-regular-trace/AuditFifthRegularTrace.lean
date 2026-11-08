module
import all IntegralFieldTrace318
import all AffineDominantTrace318
import all FifthChartTrace318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`IntegralFieldTrace318,`AffineDominantTrace318,`FifthChartTrace318]
  for name in #[`IntegralFieldTrace318.exists_value,`IntegralFieldTrace318.trace,`IntegralFieldTrace318.trace_embedding,`IntegralFieldTrace318.trace_algebraMap,`IntegralFieldTrace318.unique,`AffineDominantTrace318.trace,`AffineDominantTrace318.embedding,`AffineDominantTrace318.pullback,`AffineDominantTrace318.linearity,`FifthChartTrace318.generic_finite,`FifthChartTrace318.trace,`FifthChartTrace318.original_generic_trace,`FifthChartTrace318.trace_pullback,`FifthChartTrace318.linearity,`FifthChartTrace318.zero_of_generic_trace] do
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
  unless found == 3 do throwError "Expected three modules, found {found}"
  logInfo m!"FIFTH_REGULAR_TRACE_AUDIT_PASS declarations={checked} modules={found}"
