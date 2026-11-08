module
import all FifthNormCommonRefinement318
import all FifthNormCoverIso318
import all FifthNormChosenSourceIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthNormCommonRefinement318, `FifthNormCoverIso318, `FifthNormChosenSourceIso318]
  for name in #[`FifthNormCommonRefinement318.left_eq, `FifthNormCommonRefinement318.right_eq, `FifthNormCommonRefinement318.iso, `FifthNormCoverIso318.iso, `FifthNormCoverIso318.chosenIso, `FifthNormCoverIso318.chosen_hom_inv, `FifthNormCoverIso318.chosen_inv_hom, `FifthNormChosenSourceIso318.iso, `FifthNormChosenSourceIso318.hom_inv, `FifthNormChosenSourceIso318.inv_hom] do
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
  logInfo m!"NORM_COVER_ISOMORPHISM_AUDIT_PASS declarations={checked} modules={found}"
