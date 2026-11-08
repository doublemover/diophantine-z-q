module
import all ActualInfinityEquation318
import all AnalyticScalingGerm318
import all ArithmeticPointTopology318
import all InfinityBranchUniqueness318
import all IntegralPeriodBasis318
import all LinearScalingGerm318
import all ModularArithmeticCoordinates318
import all ModularCoordinateProper318
import all ScaledCoordinateGerm318
import all ScaledPeriodLattice318
import all ThirdArithmeticHolomorphic318
import all ThirdPeriodNormalConvergence318
import all ThirdPeriodSummands318
import all UniformPeriodBounds318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ActualInfinityEquation318,`AnalyticScalingGerm318,`ArithmeticPointTopology318,`InfinityBranchUniqueness318,`IntegralPeriodBasis318,`LinearScalingGerm318,`ModularArithmeticCoordinates318,`ModularCoordinateProper318,`ScaledCoordinateGerm318,`ScaledPeriodLattice318,`ThirdArithmeticHolomorphic318,`ThirdPeriodNormalConvergence318,`ThirdPeriodSummands318,`UniformPeriodBounds318]
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
  logInfo m!"RECOVERY_AUDIT_PASS declarations={count} modules={found}"
