module
import all RelativeLaurentScalar318
import all RelativeLaurentClearing318
import all RelativeLaurentGeneratorBound318
import all RelativePolynomialChartGenerators318
import all RelativePolynomialChartBound318
import all ScalarExtensionOriginalSpan318
import all RelativeLocalizedChartBound318
import all RelativeLocalizedChartMap318
import all RelativeLocalizedChartVanishing318
import all TensorPushoutModule318
import all AffineModuleBaseChange318
import all OriginalLineAffineModel318
import all OriginalLineAffineBaseChange318
import all SchemeIsoPushforwardRecovery318
import all AffineTensorLinePushforward318
import all AdjunctionOriginalUnitTransport318
import all AffineGlobalSectionCoherence318
import all TildePullbackMate318
import all OriginalLineBaseChangeUnit318
import all OriginalTensorChartRestriction318
import all OriginalAffineOverlapSpan318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RelativeLaurentScalar318,`RelativeLaurentClearing318,`RelativeLaurentGeneratorBound318,`RelativePolynomialChartGenerators318,`RelativePolynomialChartBound318,`ScalarExtensionOriginalSpan318,`RelativeLocalizedChartBound318,`RelativeLocalizedChartMap318,`RelativeLocalizedChartVanishing318,`TensorPushoutModule318,`AffineModuleBaseChange318,`OriginalLineAffineModel318,`OriginalLineAffineBaseChange318,`SchemeIsoPushforwardRecovery318,`AffineTensorLinePushforward318,`AdjunctionOriginalUnitTransport318,`AffineGlobalSectionCoherence318,`TildePullbackMate318,`OriginalLineBaseChangeUnit318,`OriginalTensorChartRestriction318,`OriginalAffineOverlapSpan318]
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
