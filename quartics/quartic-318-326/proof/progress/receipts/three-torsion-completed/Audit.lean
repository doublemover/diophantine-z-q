module
import all CompletedTangentRestriction318
import all ThreeTorsionCompletedDoubling318
import all ThreeTorsionCompletedTripling318
import all ThreeTorsionTriplingFiber318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`CompletedTangentRestriction318, `ThreeTorsionCompletedDoubling318, `ThreeTorsionCompletedTripling318, `ThreeTorsionTriplingFiber318]
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
  logInfo m!"THREE_TORSION_COMPLETED_AUDIT_PASS declarations={checked} modules={found}"
