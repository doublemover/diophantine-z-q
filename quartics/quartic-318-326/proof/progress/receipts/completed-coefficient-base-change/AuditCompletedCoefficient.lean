module
import all FinitePairCoefficient318
import all FiniteOutputCoefficient318
import all InfinityOutputCoefficient318
import all FiniteCoefficientNaturality318
import all CompletedCoefficientProduct318
import all CompletedAdditionCoefficient318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FinitePairCoefficient318,`FiniteOutputCoefficient318,`InfinityOutputCoefficient318,`FiniteCoefficientNaturality318,`CompletedCoefficientProduct318,`CompletedAdditionCoefficient318]
  for name in #[`FinitePairCoefficient318.localMap_base,`FiniteOutputCoefficient318.chord_output,`FiniteOutputCoefficient318.tangent_output,`InfinityOutputCoefficient318.output,`FiniteCoefficientNaturality318.coordinate,`CompletedCoefficientProduct318.finite_addition,`CompletedAdditionCoefficient318.addition,`CompletedAdditionCoefficient318.doubling,`CompletedAdditionCoefficient318.tripling] do
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
  unless found == 6 do throwError "Expected six modules, found {found}"
  logInfo m!"COMPLETED_COEFFICIENT_AUDIT_PASS declarations={checked} modules={found}"
