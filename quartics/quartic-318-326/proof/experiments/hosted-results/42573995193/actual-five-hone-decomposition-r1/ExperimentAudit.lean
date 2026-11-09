module
import all StructureAdditiveSheaf318
import all NormalizedStructureTrace318
import all ActualQuotientSheafRetraction318
import all SheafCohomologyRetraction318
import all ActualQuotientHOne318
import all SheafInverseImageConstants318
import all AdjunctionExtOneInjection318
import all SourceCohomologyComparison318
import all SchemeSourceCohomology318
import all ActualSourceHOnePullbacks318
import all PrincipalFractionClearing318
import all PrincipalCocycleSplit318
import all ActualPrincipalSections318
import all ActualPrincipalCocycle318
import all AffinePrincipalLocalLifts318
import all AdditiveSheafSections318
import all AffineStructureSectionLifting318
import all OpenImmersionAdditiveRestriction318
import all AffineOpenSectionLifting318
import all AdjunctionExtOneSurjection318
import all AffineStructureDirectImage318
import all AffineHOneComparison318
import all ActualSourceHOneTransfers318
import all SplitAdditiveRetraction318
import all FiniteSplitTransfer318
import all ActualFiveHOneDecomposition318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`StructureAdditiveSheaf318,`NormalizedStructureTrace318,`ActualQuotientSheafRetraction318,`SheafCohomologyRetraction318,`ActualQuotientHOne318,`SheafInverseImageConstants318,`AdjunctionExtOneInjection318,`SourceCohomologyComparison318,`SchemeSourceCohomology318,`ActualSourceHOnePullbacks318,`PrincipalFractionClearing318,`PrincipalCocycleSplit318,`ActualPrincipalSections318,`ActualPrincipalCocycle318,`AffinePrincipalLocalLifts318,`AdditiveSheafSections318,`AffineStructureSectionLifting318,`OpenImmersionAdditiveRestriction318,`AffineOpenSectionLifting318,`AdjunctionExtOneSurjection318,`AffineStructureDirectImage318,`AffineHOneComparison318,`ActualSourceHOneTransfers318,`SplitAdditiveRetraction318,`FiniteSplitTransfer318,`ActualFiveHOneDecomposition318]
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
