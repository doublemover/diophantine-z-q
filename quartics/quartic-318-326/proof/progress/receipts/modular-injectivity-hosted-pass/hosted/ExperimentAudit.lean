module
import all LinearScalingGerm318
import all ScaledPeriodLattice318
import all IntegralPeriodBasis318
import all ActualJOrbitClassification318
import all ArithmeticComparisonInjective318
import all ArithmeticComparisonHomeomorph318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`LinearScalingGerm318,`ScaledPeriodLattice318,`IntegralPeriodBasis318,`ActualJOrbitClassification318,`ArithmeticComparisonInjective318,`ArithmeticComparisonHomeomorph318]
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
