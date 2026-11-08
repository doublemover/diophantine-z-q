module
import all ReciprocalBaseFraction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ReciprocalRatFunc318, `ReciprocalBaseFraction318]
  for n in #[`ReciprocalRatFunc318.inversion, `ReciprocalRatFunc318.twice,
      `ReciprocalRatFunc318.inverse_fractionRing, `ReciprocalBaseFraction318.baseFieldMap,
      `ReciprocalBaseFraction318.actual_fractionField, `ReciprocalBaseFraction318.original_field_square] do
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
  logInfo m!"RECIPROCAL_FRACTION_AUDIT_PASS declarations={count} modules={found}"
