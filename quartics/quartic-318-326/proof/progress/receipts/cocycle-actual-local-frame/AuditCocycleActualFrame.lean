module
import all CocycleActualLocalFrame318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`CocycleActualLocalFrame318]
  for name in #[`CocycleActualLocalFrame318.projection,`CocycleActualLocalFrame318.projectionInverse,`CocycleActualLocalFrame318.inverse_projection,`CocycleActualLocalFrame318.projection_inverse,`CocycleActualLocalFrame318.projectionIso,`CocycleActualLocalFrame318.transpose,`CocycleActualLocalFrame318.transpose_eq,`CocycleActualLocalFrame318.transpose_iso,`CocycleActualLocalFrame318.frame,`CocycleActualLocalFrame318.frame_hom_inv,`CocycleActualLocalFrame318.frame_inv_hom,`CocycleActualLocalFrame318.locallyFree] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"COCYCLE_ACTUAL_FRAME_AUDIT_PASS declarations={checked} modules={found}"
