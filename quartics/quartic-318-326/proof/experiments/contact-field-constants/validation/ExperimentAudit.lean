module
import all GeometricIntegralConstants318
import all ProperChartConstants318
import all ContactFieldAffineChart318
import all ContactFieldConstants318
import all FourRootPointTorsor318
import all RationalFourRootFiber318
import all RationalContactPoint318
import all ContactFieldSection318
import all OriginalLineAutomorphismLocal318
import all OriginalLineAutomorphismScalar318
import all OriginalLineAutomorphismEquiv318
import all OriginalModuleScalarPullback318
import all OriginalLineAutPullback318
import all ContactFieldLineRigidity318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`GeometricIntegralConstants318,`ProperChartConstants318,`ContactFieldAffineChart318,`ContactFieldConstants318,`FourRootPointTorsor318,`RationalFourRootFiber318,`RationalContactPoint318,`ContactFieldSection318,`OriginalLineAutomorphismLocal318,`OriginalLineAutomorphismScalar318,`OriginalLineAutomorphismEquiv318,`OriginalModuleScalarPullback318,`OriginalLineAutPullback318,`ContactFieldLineRigidity318]
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
