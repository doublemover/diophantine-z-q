module
import all FifthInvariantGlobalEquiv318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`FifthInvariantGlobalEquiv318]
  for name in #[`FifthInvariantGlobalEquiv318.equiv,`FifthInvariantGlobalEquiv318.pullback_retraction,`FifthInvariantGlobalEquiv318.retraction_pullback,`FifthInvariantGlobalEquiv318.retraction_fifth,`FifthInvariantGlobalEquiv318.retraction_complementary] do
    unless env.contains name do throwError "Missing endpoint {name}"
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
  logInfo m!"FIFTH_GLOBAL_OMEGA_EQUIV_AUDIT_PASS declarations={n} modules={found}"
