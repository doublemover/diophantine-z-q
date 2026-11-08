module
import all CompletedCharacterOpenNorm318
import all CompletedCharacterSheafNorm318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`CompletedCharacterOpenNorm318,`CompletedCharacterSheafNorm318]
  for name in #[`CompletedCharacterOpenNorm318.original_generic_norm,
      `CompletedCharacterOpenNorm318.pullback,`CompletedCharacterOpenNorm318.restrict,
      `CompletedCharacterOpenNorm318.unit_pullback,`CompletedCharacterSheafNorm318.pullback_norm,
      `CompletedCharacterSheafNorm318.original_value] do
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
  unless found==2 do throwError "Expected two modules, found {found}"
  logInfo m!"CHARACTER_OPEN_NORM_AUDIT_PASS declarations={n} modules={found}"
