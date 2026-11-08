module
import all LineClassPullbackLaws318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LineClassPullbackLaws318]
  for n in #[`LineClassPullbackLaws318.identityIso,`LineClassPullbackLaws318.compositionIso,
      `LineClassPullbackLaws318.identity_hom_inv,`LineClassPullbackLaws318.identity_inv_hom,
      `LineClassPullbackLaws318.composition_hom_inv,`LineClassPullbackLaws318.composition_inv_hom,
      `LineClassPullbackLaws318.pullback_identity,`LineClassPullbackLaws318.pullback_composition,
      `LineClassPullbackLaws318.pullback_identity_function,`LineClassPullbackLaws318.pullback_composition_function] do
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
  logInfo m!"LINE_CLASS_PULLBACK_LAWS_AUDIT_PASS declarations={count} modules={found}"
