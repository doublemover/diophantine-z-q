module
import all OriginalLineAffineModel318
import all LaurentVectorFiltration318
import all LaurentTransitionBounds318
import all LaurentCechFinite318
import all LaurentCechSectionsFinite318
import all LaurentOriginalPolynomialCharts318
import all OriginalLineFiniteFlatPID318
import all ContactOriginalLineFiniteChart318
import all ContactWholeInfinityAlgebra318
import all ContactWholeInfinityScheme318
import all ContactOriginalLineBothCharts318
import all OriginalLaurentProjectiveOverlap318
import all ContactOriginalLaurentOverlap318
import all ContactOriginalLineOverlap318
import all OriginalLineAffineBaseChange318
import all OriginalAffineMapSections318
import all ContactOverlapTensorCharts318
import all ContactOriginalModuleOverlap318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`OriginalLineAffineModel318,`LaurentVectorFiltration318,`LaurentTransitionBounds318,`LaurentCechFinite318,`LaurentCechSectionsFinite318,`LaurentOriginalPolynomialCharts318,`OriginalLineFiniteFlatPID318,`ContactOriginalLineFiniteChart318,`ContactWholeInfinityAlgebra318,`ContactWholeInfinityScheme318,`ContactOriginalLineBothCharts318,`OriginalLaurentProjectiveOverlap318,`ContactOriginalLaurentOverlap318,`ContactOriginalLineOverlap318,`OriginalLineAffineBaseChange318,`OriginalAffineMapSections318,`ContactOverlapTensorCharts318,`ContactOriginalModuleOverlap318]
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
