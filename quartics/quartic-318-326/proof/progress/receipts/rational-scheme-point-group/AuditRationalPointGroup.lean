module
import all RationalSchemePointOperations318
import all RationalSchemePointAssociativity318
import all RationalSchemePointGroup318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`RationalSchemePointOperations318,`RationalSchemePointAssociativity318,`RationalSchemePointGroup318]
  for name in #[`RationalSchemePointOperations318.Points,`RationalSchemePointOperations318.zero_sum,`RationalSchemePointOperations318.neg_sum,`RationalSchemePointAssociativity318.sum_assoc,`RationalSchemePointGroup318.group,`RationalSchemePointGroup318.zero_val,`RationalSchemePointGroup318.neg_val,`RationalSchemePointGroup318.add_val,`RationalSchemePointGroup318.precomposeHom] do
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
  logInfo m!"RATIONAL_SCHEME_POINT_GROUP_AUDIT_PASS declarations={checked} modules={found}"
