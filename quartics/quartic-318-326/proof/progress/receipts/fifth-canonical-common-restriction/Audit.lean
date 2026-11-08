module
import all FifthCanonicalCommonRestriction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`FifthCanonicalCommonRestriction318]
  unless env.contains `FifthCanonicalCommonRestriction318.restrict do
    throwError "Missing canonical restriction"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==1 do throwError "Expected one module, found {found}"
  logInfo m!"FIFTH_CANONICAL_COMMON_AUDIT_PASS declarations={n} modules={found}"
