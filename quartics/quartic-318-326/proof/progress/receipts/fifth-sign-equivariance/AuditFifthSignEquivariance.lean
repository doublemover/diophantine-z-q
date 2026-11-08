module
import all FifthSignAffine318
import all FifthSignGlobal318
import all FifthSignCharacter318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FifthSignAffine318,`FifthSignGlobal318,`FifthSignCharacter318]
  for name in #[`FifthSignAffine318.positive,`FifthSignAffine318.negative,`FifthSignGlobal318.positive,`FifthSignGlobal318.negative,`FifthSignGlobal318.equivariant,`FifthSignGlobal318.all_tests,`FifthSignCharacter318.fixed_iff,`FifthSignCharacter318.targetIso,`FifthSignCharacter318.target_twice,`FifthSignCharacter318.zero_fixed] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 3 do throwError "Expected three modules, found {found}"
  logInfo m!"FIFTH_SIGN_EQUIVARIANCE_AUDIT_PASS declarations={checked} modules={found}"
