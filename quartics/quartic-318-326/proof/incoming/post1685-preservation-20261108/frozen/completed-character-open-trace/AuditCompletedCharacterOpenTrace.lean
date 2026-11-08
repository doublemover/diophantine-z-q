module
import all CompletedCharacterTraceBasis318
import all CompletedCharacterOpenTrace318
import all CompletedCharacterTraceAverage318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`CompletedCharacterTraceBasis318,`CompletedCharacterOpenTrace318,`CompletedCharacterTraceAverage318]
  for name in #[`CompletedCharacterTraceBasis318.chart_normal,`CompletedCharacterTraceBasis318.chart_cover,`CompletedCharacterTraceBasis318.hasBasis,`CompletedCharacterTraceBasis318.generic_finite,`CompletedCharacterOpenTrace318.trace,`CompletedCharacterOpenTrace318.original_generic_trace,`CompletedCharacterOpenTrace318.restrict,`CompletedCharacterOpenTrace318.trace_pullback,`CompletedCharacterOpenTrace318.linearity,`CompletedCharacterOpenTrace318.transfer,`CompletedCharacterTraceAverage318.scalar,`CompletedCharacterTraceAverage318.generic_scalar,`CompletedCharacterTraceAverage318.average,`CompletedCharacterTraceAverage318.average_restrict,`CompletedCharacterTraceAverage318.average_pullback,`CompletedCharacterTraceAverage318.average_linearity,`CompletedCharacterTraceAverage318.original_generic_average,`CompletedCharacterTraceAverage318.transfer,`CompletedCharacterTraceAverage318.projection_twice,`CompletedCharacterTraceAverage318.projection_eq_iff] do
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
  logInfo m!"COMPLETED_CHARACTER_OPEN_TRACE_AUDIT_PASS declarations={checked} modules={found}"
