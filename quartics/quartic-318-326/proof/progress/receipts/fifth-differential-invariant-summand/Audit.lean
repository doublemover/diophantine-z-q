module
import all FifthDifferentialInvariantSummand318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`FifthDifferentialInvariantSummand318.average_fixed,
    `FifthDifferentialInvariantSummand318.average_eq_of_fixed,
    `FifthDifferentialInvariantSummand318.average_eq_iff,
    `FifthDifferentialInvariantSummand318.range_average,
    `FifthDifferentialInvariantSummand318.retraction,
    `FifthDifferentialInvariantSummand318.retraction_inclusion] do
    unless env.contains name do throwError "Missing required endpoint: {name}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module == `FifthDifferentialInvariantSummand318 then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        count := count+1
  unless found == 1 do throwError "Expected one module, found {found}"
  logInfo m!"FIFTH_DIFFERENTIAL_INVARIANT_SUMMAND_AUDIT_PASS declarations={count} modules={found}"
