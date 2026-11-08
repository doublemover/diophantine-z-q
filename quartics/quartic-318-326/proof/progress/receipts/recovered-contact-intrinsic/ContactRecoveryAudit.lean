module
import all EtaleDifferentialFrame318
import all ContactDifferentialFrames318
import all ContactFrameNormalization318
import all ContactIntrinsicDifferentials318
import all ContactIntrinsicFrames318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`EtaleDifferentialFrame318,`ContactDifferentialFrames318,`ContactFrameNormalization318,`ContactIntrinsicDifferentials318,`ContactIntrinsicFrames318]
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
  logInfo m!"CONTACT_RECOVERY_AUDIT_PASS declarations={count} modules={found}"
