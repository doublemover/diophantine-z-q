module
import all IntrinsicDifferentialGlobalScalars318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.contains `IntrinsicDifferentialGlobalScalars318.globalSection_smul do
    throwError "Missing actual globalSection scalar endpoint"
  let mut found := false
  let mut checked : Nat := 0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module == `IntrinsicDifferentialGlobalScalars318 then
      found := true
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs}"
  unless found do throwError "Missing target module"
  logInfo m!"GLOBAL_DIFFERENTIAL_SCALARS_AUDIT_PASS declarations={checked} modules=1"
