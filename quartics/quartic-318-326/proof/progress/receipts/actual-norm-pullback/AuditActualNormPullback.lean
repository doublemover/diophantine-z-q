module
import all LinePullbackTransitions318
import all FifthNormPullback318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LinePullbackTransitions318, `FifthNormPullback318]
  for name in #[`LinePullbackTransitions318.cocycle, `FifthNormPullback318.coherent, `FifthNormPullback318.fixedIso, `FifthNormPullback318.iso, `FifthNormPullback318.hom_inv, `FifthNormPullback318.inv_hom, `FifthNormPullback318.lineIso, `FifthNormPullback318.norm_pullback, `FifthNormPullback318.kernel_power] do
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
  logInfo m!"ACTUAL_NORM_PULLBACK_AUDIT_PASS declarations={checked} modules={found}"
