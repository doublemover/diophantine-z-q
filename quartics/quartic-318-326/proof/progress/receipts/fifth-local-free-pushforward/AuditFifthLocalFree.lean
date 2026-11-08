module
import all FiniteFlatPrincipalBasis318
import all PrincipalBasisTransport318
import all AffinePrincipalBasis318
import all FifthPushforwardModules318
import all FifthPrincipalNeighborhood318
import all FiniteFreeGenericTransfer318
import all FifthLocalMatrixTransfer318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FiniteFlatPrincipalBasis318,`PrincipalBasisTransport318,`AffinePrincipalBasis318,`FifthPushforwardModules318,`FifthPrincipalNeighborhood318,`FiniteFreeGenericTransfer318,`FifthLocalMatrixTransfer318]
  for name in #[`FiniteFlatPrincipalBasis318.exists_basis,`FiniteFlatPrincipalBasis318.exists_basis_of_rank,`PrincipalBasisTransport318.basis,`AffinePrincipalBasis318.sourceOpen_eq,`AffinePrincipalBasis318.basis,`FifthPushforwardModules318.rank_eight,`FifthPushforwardModules318.exists_principal_basis,`FifthPrincipalNeighborhood318.exists_basis,`FifthPrincipalNeighborhood318.cover,`FiniteFreeGenericTransfer318.faithful,`FiniteFreeGenericTransfer318.trace_germ,`FiniteFreeGenericTransfer318.norm_germ,`FifthLocalMatrixTransfer318.trace_eq,`FifthLocalMatrixTransfer318.norm_eq,`FifthLocalMatrixTransfer318.local_control] do
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
  unless found == 7 do throwError "Expected seven modules, found {found}"
  logInfo m!"FIFTH_LOCAL_FREE_AUDIT_PASS declarations={checked} modules={found}"
