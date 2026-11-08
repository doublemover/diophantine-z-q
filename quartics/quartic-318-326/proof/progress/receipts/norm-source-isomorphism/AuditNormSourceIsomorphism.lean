module
import all LineFrameIsoTransport318
import all LineFrameIsoCocycle318
import all FifthNormSourceIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineFrameIsoTransport318, `LineFrameIsoCocycle318, `FifthNormSourceIso318]
  for name in #[`LineFrameIsoTransport318.coordinates, `LineFrameIsoTransport318.inverse_coordinates, `LineFrameIsoCocycle318.scalar, `LineFrameIsoCocycle318.cocycle_eq, `LineFrameIsoCocycle318.inverseImage_eq, `FifthNormSourceIso318.iso, `FifthNormSourceIso318.hom_inv, `FifthNormSourceIso318.inv_hom] do
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
  logInfo m!"NORM_SOURCE_ISOMORPHISM_AUDIT_PASS declarations={checked} modules={found}"
