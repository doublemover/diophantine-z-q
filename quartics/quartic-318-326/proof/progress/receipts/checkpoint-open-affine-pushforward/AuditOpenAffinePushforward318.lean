module
import all AffinePullbackStructure318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`OpenPullbackStructure318, `AffinePullbackStructure318]
  for n in #[`OpenPullbackStructure318.ringIso, `OpenPullbackStructure318.scalar_square,
      `OpenPullbackStructure318.natural, `OpenPullbackStructure318.iso,
      `OpenPullbackStructure318.iso_component, `OpenPullbackStructure318.iso_hom_inv,
      `OpenPullbackStructure318.iso_inv_hom, `AffinePullbackStructure318.square,
      `AffinePullbackStructure318.iso, `AffinePullbackStructure318.iso_component,
      `AffinePullbackStructure318.iso_hom_inv, `AffinePullbackStructure318.iso_inv_hom] do
    unless env.contains n do throwError "Missing endpoint {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for i in [:env.header.modules.size] do
    if modules.contains env.header.modules[i]!.module then
      found := found + 1
      for n in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms n
        for a in axioms do
          unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
            throwError "Forbidden axiom {a} in {n}"
        logInfo m!"AXIOM_CHECK {n}: {axioms}"
        count := count + 1
  unless found == 2 do throwError "Expected two target modules, found {found}"
  logInfo m!"OPEN_AFFINE_PUSHFORWARD_AUDIT_PASS declarations={count} modules={found}"
