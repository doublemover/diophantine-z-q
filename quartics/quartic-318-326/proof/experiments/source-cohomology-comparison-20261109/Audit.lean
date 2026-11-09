module
import all StructureAdditiveSheaf318
import all NormalizedStructureTrace318
import all ActualQuotientSheafRetraction318
import all SheafCohomologyRetraction318
import all ActualQuotientHOne318
import all SheafInverseImageConstants318
import all AdjunctionExtOneInjection318
import all SourceCohomologyComparison318
import all SchemeSourceCohomology318
import all ActualSourceHOnePullbacks318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`StructureAdditiveSheaf318, `NormalizedStructureTrace318,
    `ActualQuotientSheafRetraction318, `SheafCohomologyRetraction318, `ActualQuotientHOne318,
    `SheafInverseImageConstants318, `AdjunctionExtOneInjection318, `SourceCohomologyComparison318, `SchemeSourceCohomology318, `ActualSourceHOnePullbacks318]
  for name in #[`StructureAdditiveSheaf318.pushed_eq,
    `NormalizedStructureTrace318.pullback_retraction,
    `ActualQuotientSheafRetraction318.character_split,
    `ActualQuotientSheafRetraction318.fifth_split,
    `SheafCohomologyRetraction318.transfer_pullback,
    `SheafCohomologyRetraction318.pullback_HZero,
    `SheafCohomologyRetraction318.transfer_HZero,
    `ActualQuotientHOne318.character_split_all,
    `ActualQuotientHOne318.fifth_split_all,
    `ActualQuotientHOne318.character_h1_injective,
    `ActualQuotientHOne318.fifth_h1_injective,
    `ActualQuotientHOne318.character_h1_transfer_surjective,
    `ActualQuotientHOne318.fifth_h1_transfer_surjective,
    `AdjunctionExtOneInjection318.mate_one_injective,
    `SourceCohomologyComparison318.comparison_mkZero,
    `SourceCohomologyComparison318.comparison_naturality,
    `SourceCohomologyComparison318.comparison_zero_bijective,
    `SourceCohomologyComparison318.comparison_one_injective,
    `SchemeSourceCohomology318.pullback_one_injective_of_retraction,
    `ActualSourceHOnePullbacks318.character_injective,
    `ActualSourceHOnePullbacks318.fifth_injective,
    `ActualSourceHOnePullbacks318.character_factorization,
    `ActualSourceHOnePullbacks318.fifth_factorization] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do
        throwError "Expected proposition: {name}"
  let mut declarations : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axioms}"
        declarations := declarations + 1
  unless found == modules.size do
    throwError "Expected {modules.size} modules, found {found}"
  logInfo m!"SOURCE_COHOMOLOGY_COMPARISON_AUDIT_PASS declarations={declarations} modules={found}"
