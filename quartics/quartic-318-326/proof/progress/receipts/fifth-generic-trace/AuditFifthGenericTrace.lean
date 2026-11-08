module
import all FifthGenericTrace318
import all FifthTraceCharacters318
import all FifthTraceProjection318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthGenericTrace318,`FifthTraceCharacters318,`FifthTraceProjection318]
  for name in #[`FifthGenericTrace318.trace,`FifthGenericTrace318.trace_pullback,`FifthGenericTrace318.original_trace,`FifthGenericTrace318.original_trace_sum,`FifthTraceCharacters318.invariant,`FifthTraceCharacters318.zero_of_anti,`FifthTraceCharacters318.separating_sign,`FifthTraceCharacters318.root_trace_zero,`FifthTraceCharacters318.actual_root_trace_zero,`FifthTraceCharacters318.original_four_trace_zero,`FifthTraceProjection318.retraction_pullback,`FifthTraceProjection318.projection_twice,`FifthTraceProjection318.projection_range,`FifthTraceProjection318.retraction_surjective] do
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
  logInfo m!"FIFTH_GENERIC_TRACE_AUDIT_PASS declarations={checked} modules={found}"
