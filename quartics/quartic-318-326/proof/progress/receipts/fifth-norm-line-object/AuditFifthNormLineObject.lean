module
import all FifthLineReconstruction318
import all FifthNormLineObject318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthLineReconstruction318, `FifthNormLineObject318]
  for name in #[`FifthLineReconstruction318.sourceIso, `FifthLineReconstruction318.hom_inv, `FifthLineReconstruction318.inv_hom, `FifthLineReconstruction318.original_transition, `FifthNormLineObject318.object, `FifthNormLineObject318.frame, `FifthNormLineObject318.locallyFree, `FifthNormLineObject318.norm_original_transition] do
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
  logInfo m!"FIFTH_NORM_LINE_OBJECT_AUDIT_PASS declarations={checked} modules={found}"
