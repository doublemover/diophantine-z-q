module
import all FifthCompletedProper318
import all FifthCompletedFunctionField318
import all FifthCompletedDegree318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FifthCompletedProper318, `FifthCompletedFunctionField318, `FifthCompletedDegree318]
  for name in #[`FifthCompletedProper318.infinityShort_injective, `FifthCompletedProper318.proper, `FifthCompletedProper318.dominant, `FifthCompletedProper318.surjective, `FifthCompletedFunctionField318.sourceEquiv, `FifthCompletedFunctionField318.targetEquiv, `FifthCompletedDegree318.pullback_on_order, `FifthCompletedDegree318.actual_field_square, `FifthCompletedDegree318.actual_generic_degree_eight] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"FIFTH_GENERIC_DEGREE_AUDIT_PASS declarations={checked} modules={found}"
