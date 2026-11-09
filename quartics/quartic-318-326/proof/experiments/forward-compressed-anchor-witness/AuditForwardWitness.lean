module
import all CompressedAnchorWitness318
import all ReciprocalChartWitness318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`CompressedAnchorWitness318,`ReciprocalChartWitness318]
  let required : Array Name := #[`CompressedAnchorWitness318.literal_rows,
    `CompressedAnchorWitness318.reconstruct_original,
    `ReciprocalChartWitness318.first39_rows,
    `ReciprocalChartWitness318.prefix_hasSolution]
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
