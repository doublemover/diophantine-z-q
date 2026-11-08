module
import all FifthSourceOverlap318
import all FifthGlobalCompatibility318
import all FifthCompletedGlobal318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthSourceOverlap318, `FifthGlobalCompatibility318, `FifthCompletedGlobal318]
  for name in #[`FifthSourceOverlap318.lift_raw, `FifthSourceOverlap318.shortMap_raw, `FifthSourceOverlap318.finite_restriction, `FifthGlobalCompatibility318.short_maps_agree, `FifthGlobalCompatibility318.maps_agree, `FifthCompletedGlobal318.map, `FifthCompletedGlobal318.on_finite, `FifthCompletedGlobal318.on_infinity, `FifthCompletedGlobal318.over_Q, `FifthCompletedGlobal318.unique] do
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
  logInfo m!"FIFTH_GLOBAL_MAP_AUDIT_PASS declarations={checked} modules={found}"
