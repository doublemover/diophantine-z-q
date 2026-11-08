module
import all CocycleCanonicalTransitions318
import all CocycleEqualityTransport318
import all CocycleRefinementIso318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CocycleCanonicalTransitions318,`CocycleEqualityTransport318,`CocycleRefinementIso318]
  for n in #[`CocycleCanonicalTransitions318.coordinate,`CocycleCanonicalTransitions318.inverse_relation,
      `CocycleCanonicalTransitions318.cocycle_eq,`CocycleEqualityTransport318.changeTarget_coefficient,
      `CocycleRefinementIso318.extracted,`CocycleRefinementIso318.iso,
      `CocycleRefinementIso318.hom_inv,`CocycleRefinementIso318.inv_hom,
      `CocycleRefinementIso318.hom_coefficient,`CocycleRefinementIso318.inv_coordinate,
      `CocycleRefinementIso318.original_frame] do
    unless env.contains n do throwError "Required endpoint missing: {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing target module"
  logInfo m!"COCYCLE_REFINEMENT_AUDIT_PASS declarations={count} modules={found}"
