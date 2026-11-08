module
import all ActualCharacterInvariantLines318
import all ActualFifthInvariantLine318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`ActualCharacterInvariantLines318,`ActualFifthInvariantLine318]
  for name in #[`ActualCharacterInvariantLines318.fixed_iff_existsUnique,
      `ActualCharacterInvariantLines318.range_parameter,`ActualCharacterInvariantLines318.parameter_injective,
      `ActualFifthInvariantLine318.fixed_iff_existsUnique,`ActualFifthInvariantLine318.range_parameter,
      `ActualFifthInvariantLine318.parameter_injective] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not a proposition: {name}"
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
  unless found==2 do throwError "Expected two modules, found {found}"
  logInfo m!"ACTUAL_INVARIANT_LINES_AUDIT_PASS declarations={n} modules={found}"
