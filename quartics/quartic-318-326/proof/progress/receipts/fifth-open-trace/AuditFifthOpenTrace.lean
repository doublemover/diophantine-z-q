module
import all AffineDominantTraceRestriction318
import all OpenDominantTraceExistence318
import all OpenDominantTrace318
import all OpenTraceSheaf318
import all FifthOpenTrace318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`AffineDominantTraceRestriction318,`OpenDominantTraceExistence318,`OpenDominantTrace318,`OpenTraceSheaf318,`FifthOpenTrace318]
  for name in #[`AffineDominantTraceRestriction318.restrict,`OpenDominantTraceExistence318.exists_value,`OpenDominantTrace318.trace_embedding,`OpenDominantTrace318.restrict,`OpenDominantTrace318.affine_eq,`OpenDominantTrace318.pullback,`OpenDominantTrace318.linearity,`OpenTraceSheaf318.transfer,`OpenTraceSheaf318.component,`OpenTraceSheaf318.scalar,`FifthOpenTrace318.original_generic_trace,`FifthOpenTrace318.restrict,`FifthOpenTrace318.trace_pullback,`FifthOpenTrace318.linearity,`FifthOpenTrace318.chart_eq,`FifthOpenTrace318.transfer,`FifthOpenTrace318.transfer_component] do
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
  logInfo m!"FIFTH_OPEN_TRACE_AUDIT_PASS declarations={checked} modules={found}"
