module
import all FiniteUnitTransferUnit318
import all CompletedCharacterNormUnit318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`FiniteUnitTransferUnit318,`CompletedCharacterNormUnit318]
  for name in #[`FiniteUnitTransferUnit318.source_cocycle_eq,`FiniteUnitTransferUnit318.target_cocycle_eq,
      `FiniteUnitTransferUnit318.hom_inv,`FiniteUnitTransferUnit318.inv_hom,
      `CompletedCharacterNormUnit318.hom_inv,`CompletedCharacterNormUnit318.inv_hom] do
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
  unless found==2 do throwError "Expected two modules, found {found}"
  logInfo m!"CHARACTER_NORM_UNIT_AUDIT_PASS declarations={n} modules={found}"
