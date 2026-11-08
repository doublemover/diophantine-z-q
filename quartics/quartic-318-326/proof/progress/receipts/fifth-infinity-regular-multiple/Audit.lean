module
import all QuadraticCoordinateDerivative318
import all FifthInfinityInvariantCoefficient318
import all FifthInfinityInvariantRestriction318
import all RegularUnitMultiple318
import all FifthInfinityRegularMultiple318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`QuadraticCoordinateDerivative318,`FifthInfinityInvariantCoefficient318,
    `FifthInfinityInvariantRestriction318,`RegularUnitMultiple318,`FifthInfinityRegularMultiple318]
  for name in #[`FifthInfinityInvariantCoefficient318.two_y_unit,
    `FifthInfinityInvariantCoefficient318.factor_unit,`FifthInfinityInvariantCoefficient318.normalized,
    `FifthInfinityInvariantRestriction318.section_restrict,`FifthInfinityInvariantRestriction318.normalized,
    `FifthInfinityRegularMultiple318.form_multiple,`FifthInfinityRegularMultiple318.section_multiple,
    `FifthInfinityRegularMultiple318.average_section_multiple] do
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
  unless found==5 do throwError "Expected five modules, found {found}"
  logInfo m!"FIFTH_INFINITY_REGULAR_MULTIPLE_AUDIT_PASS declarations={n} modules={found}"
