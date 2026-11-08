module
import all IntrinsicConstantInvariantGenerator318
import all ActualTargetRationalInvariants318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`IntrinsicConstantInvariantGenerator318, `ActualTargetRationalInvariants318]
  for n in #[`IntrinsicConstantInvariantGenerator318.constant_bijective,
      `IntrinsicConstantInvariantGenerator318.bijective, `IntrinsicConstantInvariantGenerator318.existsUnique,
      `ActualTargetRationalInvariants318.character_bijective, `ActualTargetRationalInvariants318.character_unique,
      `ActualTargetRationalInvariants318.fifth_bijective, `ActualTargetRationalInvariants318.fifth_unique] do
    unless env.contains n do throwError "Missing required endpoint: {n}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for n in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms n
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {n}"
        count := count + 1
        logInfo m!"AXIOM_CHECK {n}: {axs.toList}"
  unless found == modules.size do throwError "Missing target module"
  logInfo m!"TARGET_RATIONAL_INVARIANT_AUDIT_PASS declarations={count} modules={found}"
