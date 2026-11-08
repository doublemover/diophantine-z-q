module
import all CompletedAdditionPoints318
import all CompletedAdditionCommutative318
import all CompletedAdditionAssociativityTest318
import all CompletedAdditionAssociativity318
import all LiteralGroupAssociativity318
import all CompletedLeftInverse318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`CompletedAdditionPoints318,`CompletedAdditionCommutative318,`CompletedAdditionAssociativityTest318,`CompletedAdditionAssociativity318,`LiteralGroupAssociativity318,`CompletedLeftInverse318]
  for name in #[`CompletedAdditionPoints318.actual_add,`CompletedAdditionPoints318.sumPoint_assoc,`CompletedAdditionCommutative318.addition_commutative,`CompletedAdditionAssociativityTest318.field_test,`CompletedAdditionAssociativity318.associative_of_reduced,`LiteralGroupAssociativity318.associative,`CompletedLeftInverse318.antiDiagonal_addition] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == names.size do throwError "Missing module"
  logInfo m!"LITERAL_GROUP_LAWS_AUDIT_PASS declarations={checked} modules={found}"
