module
import all BranchOriginalCoordinate318
import all FifthBranchUnitCoefficient318
import all FifthBranchDifferential318
import all IntegralChartSectionDetection318
import all BranchIntrinsicNaturality318
import all BranchRestrictionInjective318
import all BranchSectionExtension318
import all FifthBranchCommonSection318
import all FifthBranchInvariantRestriction318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`BranchOriginalCoordinate318,`FifthBranchUnitCoefficient318,`FifthBranchDifferential318,
    `IntegralChartSectionDetection318,`BranchIntrinsicNaturality318,`BranchRestrictionInjective318,
    `BranchSectionExtension318,`FifthBranchCommonSection318,`FifthBranchInvariantRestriction318]
  for name in #[`BranchOriginalCoordinate318.coordinate_eq_root,`FifthBranchUnitCoefficient318.coefficient_unit,
      `FifthBranchDifferential318.common_eq,`FifthBranchDifferential318.frame_value,
      `BranchSectionExtension318.naturality_eq,`FifthBranchInvariantRestriction318.restrict,
      `FifthBranchInvariantRestriction318.unit_frame_and_restrict] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Endpoint is not a proposition: {name}"
  let mut n:Nat:=0
  let mut found:Nat:=0
  for idx in [:env.header.modules.size] do
    if mods.contains env.header.modules[idx]!.module then
      found:=found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        n:=n+1
  unless found==9 do throwError "Expected nine modules, found {found}"
  logInfo m!"FIFTH_BRANCH_AUDIT_PASS declarations={n} modules={found}"
