module
import all SphereInversion318
import all ReflectedDiskJoukowski318
import all ReflectedDiskJoukowskiTopology318
import all ReflectedConvexDisk318
import all PELMaximalHalfOctagonShape318
import all PELMaximalHalfOctagonSphere318
import all PELMaximalHalfOctagonCoordinates318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`SphereInversion318,`ReflectedDiskJoukowski318,`ReflectedDiskJoukowskiTopology318,`ReflectedConvexDisk318,`PELMaximalHalfOctagonShape318,`PELMaximalHalfOctagonSphere318,`PELMaximalHalfOctagonCoordinates318]
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
