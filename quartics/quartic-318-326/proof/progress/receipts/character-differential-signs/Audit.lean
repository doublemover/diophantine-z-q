module
import all UnitFrameSectionDetection318
import all WeierstrassAffineFormCancellation318
import all WeierstrassInvariantNegation318
import all WeierstrassGlobalNegation318
import all PublishedInvariantNegation318
import all ContactDifferentialCharacters318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`UnitFrameSectionDetection318,`WeierstrassAffineFormCancellation318,`WeierstrassInvariantNegation318,`WeierstrassGlobalNegation318,`PublishedInvariantNegation318,`ContactDifferentialCharacters318]
  for name in #[`UnitFrameSectionDetection318.restrict_injective,`UnitFrameSectionDetection318.cancel_scalar,`WeierstrassAffineFormCancellation318.cancel_scalar,`WeierstrassInvariantNegation318.affine,`WeierstrassGlobalNegation318.global,`PublishedInvariantNegation318.invariant_negation,`ContactDifferentialCharacters318.positive,`ContactDifferentialCharacters318.negative,`ContactDifferentialCharacters318.eigenrelation] do
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
  logInfo m!"CHARACTER_DIFFERENTIAL_SIGN_AUDIT_PASS declarations={checked} modules={found}"
