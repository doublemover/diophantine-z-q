module
import all LiteralSchemePointOperations318
import all LiteralSchemePointAssociativity318
import all LiteralSchemeCancellation318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`LiteralSchemePointOperations318,`LiteralSchemePointAssociativity318,`LiteralSchemeCancellation318]
  for name in #[`LiteralSchemePointOperations318.sum,`LiteralSchemePointAssociativity318.sum_assoc,`LiteralSchemeCancellation318.sum_left_cancel,`LiteralSchemeCancellation318.sum_eq_zero_iff,`LiteralSchemeCancellation318.tripling_zero_iff] do
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
  logInfo m!"LITERAL_SCHEME_CANCELLATION_AUDIT_PASS declarations={checked} modules={found}"
