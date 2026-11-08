module
import all EtaleDomainNormal318
import all SmoothDomainNormal318
import all CompletedRationalNormal318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`EtaleDomainNormal318, `SmoothDomainNormal318, `CompletedRationalNormal318]
  for name in #[`EtaleDomainNormal318.integrallyClosed, `SmoothDomainNormal318.integrallyClosed,
      `CompletedRationalNormal318.affine, `CompletedRationalNormal318.infinity, `CompletedRationalNormal318.both_charts] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked+1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"SMOOTH_DOMAIN_NORMALITY_AUDIT_PASS declarations={checked} modules={found}"
