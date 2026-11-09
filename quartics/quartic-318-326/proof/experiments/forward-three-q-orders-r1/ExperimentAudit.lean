module
import all ThreeCompactParameter318
import all LiteralThreeCompactParameter318
import all ThreeExceptionalParameter318
import all ActualThreeExceptionalParameter318
import all ActualThreeParameterProper318
import all ActualThreeGlobalParameter318
import all ActualThreeCuspOrbit318
import all ActualThreeCuspHomeomorph318
import all ActualThreeCuspWidths318
import all ActualThreeCuspJ318
import all ActualThreeQParameter318
import all ThreeParameterGrowth318
import all ActualThreeQMeromorphic318
import all ThreeParameterCompositionOrder318
import all ActualThreeQOrders318
import all ActualThreeInfinityUniformizer318
import all ActualThreeCuspAssignment318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ThreeCompactParameter318,`LiteralThreeCompactParameter318,`ThreeExceptionalParameter318,`ActualThreeExceptionalParameter318,`ActualThreeParameterProper318,`ActualThreeGlobalParameter318,`ActualThreeCuspOrbit318,`ActualThreeCuspHomeomorph318,`ActualThreeCuspWidths318,`ActualThreeCuspJ318,`ActualThreeQParameter318,`ThreeParameterGrowth318,`ActualThreeQMeromorphic318,`ThreeParameterCompositionOrder318,`ActualThreeQOrders318,`ActualThreeInfinityUniformizer318,`ActualThreeCuspAssignment318]
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
