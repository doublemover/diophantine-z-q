module
import all StructureAdditiveSheaf318
import all SheafCohomologyRetraction318
import all PrincipalFractionClearing318
import all PrincipalCocycleSplit318
import all ActualPrincipalSections318
import all ActualPrincipalCocycle318
import all AffinePrincipalLocalLifts318
import all AdditiveSheafSections318
import all AffineStructureSectionLifting318
import all AffineStructureHOne318
import all ActualSourceAffineHOne318
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`StructureAdditiveSheaf318, `SheafCohomologyRetraction318, `PrincipalFractionClearing318, `PrincipalCocycleSplit318, `ActualPrincipalSections318, `ActualPrincipalCocycle318, `AffinePrincipalLocalLifts318, `AdditiveSheafSections318, `AffineStructureSectionLifting318, `AffineStructureHOne318, `ActualSourceAffineHOne318]
  for name in #[`StructureAdditiveSheaf318.pushed_eq,
    `SheafCohomologyRetraction318.pullback_HZero,
    `PrincipalFractionClearing318.mem_away_iff,
    `PrincipalFractionClearing318.clear_finite,
    `PrincipalCocycleSplit318.power_coefficients,
    `PrincipalCocycleSplit318.split_of_principal_cover,
    `ActualPrincipalSections318.sections_eq_original,
    `ActualPrincipalSections318.range_embed,
    `ActualPrincipalSections318.embed_restrict,
    `ActualPrincipalCocycle318.split,
    `AdditiveSheafSections318.app_injective,
    `AffineStructureSectionLifting318.O_eq_original,
    `AffineStructureSectionLifting318.surjective,
    `AffineStructureHOne318.eq_zero,
    `AffineStructureHOne318.structureH_one_zero,
    `ActualSourceAffineHOne318.finite_chart_zero,
    `ActualSourceAffineHOne318.infinity_chart_zero,
    `ActualSourceAffineHOne318.cover_chart_zero] do
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
  logInfo m!"AFFINE_STRUCTURE_HONE_AUDIT_PASS declarations={declarations} modules={found}"
