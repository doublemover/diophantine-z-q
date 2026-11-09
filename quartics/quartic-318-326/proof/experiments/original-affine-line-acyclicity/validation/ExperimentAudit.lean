module
import all FiniteProjectiveDualFrame318
import all OriginalLineAffineModel318
import all OriginalAffineLineDualFrame318
import all ExtFiniteRetractVanishing318
import all StructureAdditiveSheaf318
import all AdditiveSheafSections318
import all PrincipalFractionClearing318
import all PrincipalCocycleSplit318
import all ActualPrincipalSections318
import all ActualPrincipalCocycle318
import all AffinePrincipalLocalLifts318
import all AffineStructureSectionLifting318
import all SheafInverseImageConstants318
import all OpenImmersionAdditiveRestriction318
import all AffineOpenSectionLifting318
import all LocalSheafCohomologySections318
import all LocalAffineStructureHOne318
import all OriginalAffineLineLocalHOne318
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FiniteProjectiveDualFrame318,`OriginalLineAffineModel318,`OriginalAffineLineDualFrame318,`ExtFiniteRetractVanishing318,`StructureAdditiveSheaf318,`AdditiveSheafSections318,`PrincipalFractionClearing318,`PrincipalCocycleSplit318,`ActualPrincipalSections318,`ActualPrincipalCocycle318,`AffinePrincipalLocalLifts318,`AffineStructureSectionLifting318,`SheafInverseImageConstants318,`OpenImmersionAdditiveRestriction318,`AffineOpenSectionLifting318,`LocalSheafCohomologySections318,`LocalAffineStructureHOne318,`OriginalAffineLineLocalHOne318]
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
