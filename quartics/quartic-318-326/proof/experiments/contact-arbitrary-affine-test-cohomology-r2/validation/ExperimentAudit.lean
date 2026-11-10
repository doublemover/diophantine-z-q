module
import all ContactWholeInfinityAlgebra318
import all ContactWholeInfinityScheme318
import all OriginalAffineTestOpen318
import all ContactOriginalAffineTestCover318
import all StructureAdditiveSheaf318
import all SheafInverseImageConstants318
import all LocalSheafCohomologySections318
import all LocalSheafCohomologyAdditive318
import all LocalCohomologyRestriction318
import all TerminalLocalCohomology318
import all OpenMayerVietoris318
import all MayerVietorisSectionKernel318
import all ExtFiniteRetractVanishing318
import all AdditiveSheafSections318
import all OriginalPrincipalLocalization318
import all OriginalPrincipalUniformClearing318
import all OriginalPrincipalCocycleRows318
import all OriginalNonreducedCocycleSplit318
import all NonreducedAffineLocalLifts318
import all NonreducedAffineSectionLifting318
import all OpenImmersionAdditiveRestriction318
import all NonreducedOpenStructureLifting318
import all NonreducedLocalStructureHOne318
import all FiniteProjectiveDualFrame318
import all OriginalLineAffineModel318
import all OriginalAffineLineDualFrame318
import all NonreducedAffineLineHOne318
import all NonreducedLineRestriction318
import all NonreducedAffineLineLifting318
import all NonreducedLineOpenLifting318
import all NonreducedLineAffineHOne318
import all NonreducedLineMayerVietoris318
import all ContactOriginalAffineTestHOne318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`ContactWholeInfinityAlgebra318,`ContactWholeInfinityScheme318,`OriginalAffineTestOpen318,`ContactOriginalAffineTestCover318,`StructureAdditiveSheaf318,`SheafInverseImageConstants318,`LocalSheafCohomologySections318,`LocalSheafCohomologyAdditive318,`LocalCohomologyRestriction318,`TerminalLocalCohomology318,`OpenMayerVietoris318,`MayerVietorisSectionKernel318,`ExtFiniteRetractVanishing318,`AdditiveSheafSections318,`OriginalPrincipalLocalization318,`OriginalPrincipalUniformClearing318,`OriginalPrincipalCocycleRows318,`OriginalNonreducedCocycleSplit318,`NonreducedAffineLocalLifts318,`NonreducedAffineSectionLifting318,`OpenImmersionAdditiveRestriction318,`NonreducedOpenStructureLifting318,`NonreducedLocalStructureHOne318,`FiniteProjectiveDualFrame318,`OriginalLineAffineModel318,`OriginalAffineLineDualFrame318,`NonreducedAffineLineHOne318,`NonreducedLineRestriction318,`NonreducedAffineLineLifting318,`NonreducedLineOpenLifting318,`NonreducedLineAffineHOne318,`NonreducedLineMayerVietoris318,`ContactOriginalAffineTestHOne318]
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
