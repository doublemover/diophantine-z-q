module
import all InfinityDiagonalDivisibility318
import all NegatedCoordinateFrameFunctor318
import all InfinityDifferentialDivisibility318
import all InfinityGlobalDifferentialRestriction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`InfinityDiagonalDivisibility318,`NegatedCoordinateFrameFunctor318,
    `InfinityDifferentialDivisibility318,`InfinityGlobalDifferentialRestriction318]
  for name in #[`InfinityDiagonalDivisibility318.quotient_fixed,`InfinityDiagonalDivisibility318.divisible,
    `NegatedCoordinateFrameFunctor318.map_frame,`InfinityDifferentialDivisibility318.fixed_factorization,
    `InfinityGlobalDifferentialRestriction318.form_action,
    `InfinityGlobalDifferentialRestriction318.invariant_factorization,
    `InfinityGlobalDifferentialRestriction318.average_factorization] do
    unless env.contains name do throwError "Missing endpoint: {name}"
  let mut n : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n := n+1
  unless found == 4 do throwError "Expected four modules, found {found}"
  logInfo m!"INFINITY_INVARIANT_DIVISIBILITY_AUDIT_PASS declarations={n} modules={found}"
