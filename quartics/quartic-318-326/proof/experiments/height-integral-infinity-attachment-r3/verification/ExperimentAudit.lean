module
import all IntegralBranchChart318
import all IntegralSourceBranches318
import all IntegralBranchFrames318
import all IntegralBranchDenominatorCover318
import all IntegralBranchLocalization318
import all IntegralInfinityChart318
import all IntegralReciprocalRootScale318
import all IntegralInfinityCommonBase318
import all IntegralInfinityCommonOrder318
import all IntegralInfinityReverseBase318
import all IntegralInfinityBaseEquiv318
import all IntegralInfinityOverlapRealization318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`IntegralBranchChart318,`IntegralSourceBranches318,`IntegralBranchFrames318,`IntegralBranchDenominatorCover318,`IntegralBranchLocalization318,`IntegralInfinityChart318,`IntegralReciprocalRootScale318,`IntegralInfinityCommonBase318,`IntegralInfinityCommonOrder318,`IntegralInfinityReverseBase318,`IntegralInfinityBaseEquiv318,`IntegralInfinityOverlapRealization318]
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
