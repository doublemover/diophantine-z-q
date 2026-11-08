module
import all CompletedCharacterPulledCocycle318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`CompletedCharacterPulledCocycle318]
  for name in #[`CompletedCharacterPulledCocycle318.transfer_eq,`CompletedCharacterPulledCocycle318.hom_inv,
      `CompletedCharacterPulledCocycle318.inv_hom] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not proposition {name}"
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
  unless found==1 do throwError "Expected one module, found {found}"
  logInfo m!"CHARACTER_PULLED_COCYCLE_AUDIT_PASS declarations={n} modules={found}"
