module
import all PELQuaternionAlgebra318
import all PELQuaternionAlternatingForm318
import all PELQuaternionRealRepresentation318
import all PELQuaternionIntegralOrder318
import all PELPrincipalOrderCoordinates318
import all PELPrincipalOrderPerfect318
import all PELQuaternionAnisotropy318
import all PELQuaternionDivision318
import all PELOrderTraceDiscriminant318
import all PELTraceDualResidues318
import all PELTraceDualSaturation318
import all PELIntegralOverorder318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`PELQuaternionAlgebra318,`PELQuaternionAlternatingForm318,`PELQuaternionRealRepresentation318,`PELQuaternionIntegralOrder318,`PELPrincipalOrderCoordinates318,`PELPrincipalOrderPerfect318,`PELQuaternionAnisotropy318,`PELQuaternionDivision318,`PELOrderTraceDiscriminant318,`PELTraceDualResidues318,`PELTraceDualSaturation318,`PELIntegralOverorder318]
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
