module
import all CompletedNegationCoefficient318
import all CoefficientSchemePoints318
import all CoefficientPointGroup318
import all CoefficientGroupAssociativity318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`CompletedNegationCoefficient318,`CoefficientSchemePoints318,`CoefficientPointGroup318,`CoefficientGroupAssociativity318]
  for name in #[`CompletedNegationCoefficient318.negation,`CoefficientSchemePoints318.equiv,`CoefficientSchemePoints318.forget_sum,`CoefficientPointGroup318.group,`CoefficientPointGroup318.addEquiv,`CoefficientGroupAssociativity318.associative] do
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
  unless found == 4 do throwError "Expected four modules, found {found}"
  logInfo m!"COEFFICIENT_GROUP_AUDIT_PASS declarations={checked} modules={found}"
