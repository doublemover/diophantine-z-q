module
import all ContactWholeInfinityAlgebra318
import all ContactWholeInfinityScheme318
import all OriginalAffineTestOpen318
import all ContactOriginalAffineTestCover318
import all OriginalLineAffineModel318
import all OriginalLineFiniteFlatPID318
import all RelativeOriginalPolynomialAlgebra318
import all RelativeOriginalChartSections318
import all RelativeOriginalAffineChart318
import all ContactOriginalRelativePolynomialCharts318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ContactWholeInfinityAlgebra318,`ContactWholeInfinityScheme318,`OriginalAffineTestOpen318,`ContactOriginalAffineTestCover318,`OriginalLineAffineModel318,`OriginalLineFiniteFlatPID318,`RelativeOriginalPolynomialAlgebra318,`RelativeOriginalChartSections318,`RelativeOriginalAffineChart318,`ContactOriginalRelativePolynomialCharts318]
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
