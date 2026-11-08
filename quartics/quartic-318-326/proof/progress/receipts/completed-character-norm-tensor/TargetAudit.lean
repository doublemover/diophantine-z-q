module
import all UnitTransferTensorIso318
import all FiniteUnitTransferTensorCommon318
import all FiniteUnitTransferTensorIso318
import all CompletedCharacterNormTensor318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`UnitTransferTensorIso318,`FiniteUnitTransferTensorCommon318,`FiniteUnitTransferTensorIso318,`CompletedCharacterNormTensor318]
  for name in #[`UnitTransferTensorIso318.tensor_cocycle,`UnitTransferTensorIso318.hom_inv,
      `UnitTransferTensorIso318.inv_hom,`FiniteUnitTransferTensorCommon318.cover,
      `FiniteUnitTransferTensorIso318.hom_inv,`FiniteUnitTransferTensorIso318.inv_hom,
      `CompletedCharacterNormTensor318.hom_inv,`CompletedCharacterNormTensor318.inv_hom,
      `CompletedCharacterNormTensor318.line_hom_inv,`CompletedCharacterNormTensor318.line_inv_hom] do
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
  unless found==4 do throwError "Expected four modules, found {found}"
  logInfo m!"CHARACTER_NORM_TENSOR_AUDIT_PASS declarations={n} modules={found}"
