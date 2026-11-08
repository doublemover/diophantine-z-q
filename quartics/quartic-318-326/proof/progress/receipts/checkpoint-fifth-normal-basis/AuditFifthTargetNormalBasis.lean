module
import all FifthTargetNormalBasis318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in #[`FifthTargetNormalBasis318.chart_cover, `FifthTargetNormalBasis318.hasBasis] do
    unless env.contains n do throwError "Missing endpoint {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for i in [:env.header.modules.size] do
    if env.header.modules[i]!.module == `FifthTargetNormalBasis318 then
      found := found + 1
      for n in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms n
        for a in axioms do
          unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
            throwError "Forbidden axiom {a} in {n}"
        logInfo m!"AXIOM_CHECK {n}: {axioms}"
        count := count + 1
  unless found == 1 do throwError "Expected one target module, found {found}"
  logInfo m!"FIFTH_TARGET_NORMAL_BASIS_AUDIT_PASS declarations={count} modules={found}"
