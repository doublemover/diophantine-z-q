module
import all CompletedCharacterRegularDescent318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`CompletedCharacterRegularDescent318]
  for name in #[`CompletedCharacterRegularDescent318.averageTop,`CompletedCharacterRegularDescent318.averageTop_pullback,`CompletedCharacterRegularDescent318.traceTop_generic,`CompletedCharacterRegularDescent318.generic_trace_pullback,`CompletedCharacterRegularDescent318.averageTop_generic,`CompletedCharacterRegularDescent318.pullback_average,`CompletedCharacterRegularDescent318.exists_target,`CompletedCharacterRegularDescent318.existsUnique_target] do
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
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"COMPLETED_CHARACTER_REGULAR_DESCENT_AUDIT_PASS declarations={checked} modules={found}"
