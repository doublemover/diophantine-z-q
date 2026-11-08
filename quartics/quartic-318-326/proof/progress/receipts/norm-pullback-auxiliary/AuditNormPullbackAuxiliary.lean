module
import all FifthNormPulledCocycle318
import all FifthNormPullbackAux318
import all FifthLineClassPullbackNormAux318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthNormPulledCocycle318, `FifthNormPullbackAux318, `FifthLineClassPullbackNormAux318]
  for name in #[`FifthNormPulledCocycle318.transfer_eq, `FifthNormPulledCocycle318.iso, `FifthNormPullbackAux318.Coherent, `FifthNormPullbackAux318.cocycle_eq, `FifthNormPullbackAux318.fixedIso, `FifthNormPullbackAux318.chosenIso, `FifthNormPullbackAux318.hom_inv, `FifthNormPullbackAux318.inv_hom, `FifthLineClassPullbackNormAux318.iso, `FifthLineClassPullbackNormAux318.norm_pullback, `FifthLineClassPullbackNormAux318.kernel_power] do
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
  logInfo m!"NORM_PULLBACK_AUXILIARY_AUDIT_PASS declarations={checked} modules={found}"
