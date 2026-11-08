module
import all CocycleGaugeMaps318
import all CocycleGaugeIso318
import all FifthNormGaugeIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CocycleGaugeMaps318, `CocycleGaugeIso318, `FifthNormGaugeIso318]
  for name in #[`CocycleGaugeMaps318.map, `CocycleGaugeMaps318.map_coefficient, `CocycleGaugeIso318.iso, `CocycleGaugeIso318.hom_inv, `CocycleGaugeIso318.inv_hom, `CocycleGaugeIso318.inv_coefficient, `FifthNormGaugeIso318.iso, `FifthNormGaugeIso318.ofOriginalFrames] do
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
  logInfo m!"NORM_COCYCLE_GAUGE_AUDIT_PASS declarations={checked} modules={found}"
