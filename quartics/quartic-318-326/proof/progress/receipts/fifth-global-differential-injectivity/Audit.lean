module
import all IntrinsicGlobalInvariantGenerator318
import all FifthGlobalScalarInjections318
import all FifthGlobalDifferentialInjective318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`IntrinsicGlobalInvariantGenerator318,`FifthGlobalScalarInjections318,`FifthGlobalDifferentialInjective318 ]
  for name in #[`IntrinsicGlobalInvariantGenerator318.bijective,`FifthGlobalScalarInjections318.multiply_injective,`FifthGlobalScalarInjections318.scalar_pullback_injective,`FifthGlobalDifferentialInjective318.injective] do
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
  unless found==3 do throwError "Expected three modules, found {found}"
  logInfo m!"FIFTH_GLOBAL_OMEGA_INJECTIVE_AUDIT_PASS declarations={n} modules={found}"
