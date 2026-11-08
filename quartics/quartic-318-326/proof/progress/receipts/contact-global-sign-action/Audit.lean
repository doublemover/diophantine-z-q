module
import all FourRootOrderSignAction318
import all ContactGlobalSignAction318
import all ContactGlobalSignFaithful318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`FourRootOrderSignAction318,`ContactGlobalSignAction318,`ContactGlobalSignFaithful318]
  for name in #[`FourRootOrderSignAction318.composition,`FourRootOrderSignAction318.identity,`ContactGlobalSignAction318.open_composition,`ContactGlobalSignAction318.open_identity,`ContactGlobalSignAction318.composition,`ContactGlobalSignAction318.identity,`ContactGlobalSignAction318.commute,`ContactGlobalSignFaithful318.injective,`ContactGlobalSignFaithful318.iso_injective,`ContactGlobalSignFaithful318.image_card] do
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
  logInfo m!"GLOBAL_SIGN_ACTION_AUDIT_PASS declarations={checked} modules={found}"
