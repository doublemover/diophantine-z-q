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
import all LocalSheafCohomologySections318
import all LocalSheafCohomologyAdditive318
import all LocalAffineStructureHOne318
import all TerminalLocalCohomology318
import all OpenMayerVietoris318
import all AffineCoverHOnePresentation318
import all ActualSourceHOnePresentation318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`StructureAdditiveSheaf318, `NormalizedStructureTrace318, `ActualQuotientSheafRetraction318, `SheafCohomologyRetraction318, `ActualQuotientHOne318, `SheafInverseImageConstants318, `AdjunctionExtOneInjection318, `SourceCohomologyComparison318, `SchemeSourceCohomology318, `ActualSourceHOnePullbacks318, `PrincipalFractionClearing318, `PrincipalCocycleSplit318, `ActualPrincipalSections318, `ActualPrincipalCocycle318, `AffinePrincipalLocalLifts318, `AdditiveSheafSections318, `AffineStructureSectionLifting318, `OpenImmersionAdditiveRestriction318, `AffineOpenSectionLifting318, `AdjunctionExtOneSurjection318, `AffineStructureDirectImage318, `AffineHOneComparison318, `ActualSourceHOneTransfers318, `LocalSheafCohomologySections318, `LocalSheafCohomologyAdditive318, `LocalAffineStructureHOne318, `TerminalLocalCohomology318, `OpenMayerVietoris318, `AffineCoverHOnePresentation318, `ActualSourceHOnePresentation318]
  for name in #[`LocalSheafCohomologySections318.sectionEquiv_naturality,
    `LocalSheafCohomologySections318.zeroEquiv_naturality,
    `LocalAffineStructureHOne318.eq_zero,
    `TerminalLocalCohomology318.integerSectionEquiv_naturality,
    `OpenMayerVietoris318.square_isPullback,
    `OpenMayerVietoris318.square_cover,
    `OpenMayerVietoris318.boundary_surjective,
    `AffineCoverHOnePresentation318.boundary_surjective,
    `ActualSourceHOnePresentation318.finite_affine,
    `ActualSourceHOnePresentation318.infinity_affine,
    `ActualSourceHOnePresentation318.cover,
    `ActualSourceHOnePresentation318.boundary_surjective] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do
        throwError "Expected proposition: {name}"
  let mut declarations : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if modules.contains env.header.modules[idx]!.module then
      found := found + 1
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axioms}"
        declarations := declarations + 1
  unless found == modules.size do
    throwError "Expected {modules.size} modules, found {found}"
  logInfo m!"SOURCE_MAYER_VIETORIS_AUDIT_PASS declarations={declarations} modules={found}"
