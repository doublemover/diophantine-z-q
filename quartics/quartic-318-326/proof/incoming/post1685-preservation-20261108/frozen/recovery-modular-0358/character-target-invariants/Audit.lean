module
import all CharacterTargetDifferentialInvariants318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`CharacterTargetDifferentialInvariants318.pullback,
      `CharacterTargetDifferentialInvariants318.fixed,
      `CharacterTargetDifferentialInvariants318.pullback_invariant] do
    unless env.contains name do throwError "Missing endpoint {name}"
  let mut found := false
  let mut checked : Nat := 0
  for idx in [:env.header.modules.size] do
    if env.header.modules[idx]!.module == `CharacterTargetDifferentialInvariants318 then
      found := true
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axs}"
  unless found do throwError "Missing target module"
  logInfo m!"CHARACTER_TARGET_INVARIANTS_AUDIT_PASS declarations={checked} modules=1"
