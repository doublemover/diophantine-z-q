module
import all FifthNormTensorCocycle318
import all FifthNormTensorIso318
import all FifthNormTensorCommon318
import all FifthNormChosenTensorIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthNormTensorCocycle318, `FifthNormTensorIso318, `FifthNormTensorCommon318, `FifthNormChosenTensorIso318]
  for name in #[`FifthNormTensorCocycle318.norm_cocycle, `FifthNormTensorIso318.iso, `FifthNormTensorIso318.hom_inv, `FifthNormTensorIso318.inv_hom, `FifthNormTensorCommon318.cover, `FifthNormTensorCommon318.leftFrame, `FifthNormTensorCommon318.rightFrame, `FifthNormTensorCommon318.leftIso, `FifthNormTensorCommon318.rightIso, `FifthNormChosenTensorIso318.sourceIso, `FifthNormChosenTensorIso318.iso, `FifthNormChosenTensorIso318.hom_inv, `FifthNormChosenTensorIso318.inv_hom] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"NORM_ACTUAL_TENSOR_AUDIT_PASS declarations={checked} modules={found}"
