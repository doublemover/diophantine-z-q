module
import all RestrictionPullbackCoherence318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`RestrictionPullbackCoherence318]
  for n in #[`RestrictionPullbackCoherence318.adjoint_restrict,
      `RestrictionPullbackCoherence318.restrict_unit,`RestrictionPullbackCoherence318.restriction_composition_unit,
      `RestrictionPullbackCoherence318.adjoint_restrict_composition,
      `RestrictionPullbackCoherence318.adjoint_restrict_component,`RestrictionPullbackCoherence318.composition] do
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
  logInfo m!"RESTRICTION_PULLBACK_COHERENCE_AUDIT_PASS declarations={count} modules={found}"
