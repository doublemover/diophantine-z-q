module
import all UnitCocycleSubopens318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`UnitCocycleSubopens318]
  for name in #[`UnitCocycleSubopens318.restrict_restrict, `UnitCocycleSubopens318.transition_mul,
      `UnitCocycleSubopens318.transition_diagonal, `UnitCocycleSubopens318.transition_mul_reverse,
      `UnitCocycleSubopens318.transition_reverse] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs.toList}"
  unless found == modules.size do throwError "Missing module"
  logInfo m!"UNIT_COCYCLE_SUBOPENS_AUDIT_PASS declarations={checked} modules={found}"
