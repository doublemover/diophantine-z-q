module
import all RealGuardWitness318
import all RealGuardTrace318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RealGuardWitness318,`RealGuardTrace318]
  let required : Array Name := #[`RealGuardWitness318.first51_rows,
    `RealGuardWitness318.actual_difference,
    `RealGuardTrace318.literal_guard,
    `RealGuardTrace318.guard_at_identity_positive,
    `RealGuardTrace318.guards_of_actual_points]
  for name in required do
    unless env.contains name do throwError "Missing required endpoint {name}"
  let mut count : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name}"
        count := count+1
  unless found == modules.size do throwError "Missing imported modules: {found}/{modules.size}"
  logInfo m!"EXPERIMENT_AUDIT_PASS declarations={count} modules={found}"
