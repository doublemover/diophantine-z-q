module
import all ContactRootReciprocals318
import all ScaledGlobalSectionRestriction318
import all FifthFormLocalCoefficients318
import all FifthFormChartRoute318
import all FifthFormAffineRestriction318
import all FifthFormGlobalRestriction318
import all FifthFormWeightedSection318
import all FifthFormCommonOpen318
import all FifthFormLocalSections318
import all FifthFormFullCompatibility318
import all FifthGlobalDifferential318
import all FiveCharacterIndependence318
import all FiveInverseRootIndependence318
import all FifthGlobalIndependence318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`ContactRootReciprocals318,`ScaledGlobalSectionRestriction318,`FifthFormLocalCoefficients318,`FifthFormChartRoute318,`FifthFormAffineRestriction318,`FifthFormGlobalRestriction318,`FifthFormWeightedSection318,`FifthFormCommonOpen318,`FifthFormLocalSections318,`FifthFormFullCompatibility318,`FifthGlobalDifferential318,`FiveCharacterIndependence318,`FiveInverseRootIndependence318,`FifthGlobalIndependence318]
  for name in #[`ContactRootReciprocals318.branch_root_unit,`ContactRootReciprocals318.infinity_reciprocal_relation,`ContactRootReciprocals318.actual_fifth_root,`FifthFormLocalCoefficients318.common_coefficient,`FifthFormCommonOpen318.global_restrict,`FifthFormCommonOpen318.branch_eq_branch,`FifthFormCommonOpen318.branch_eq_infinity,`FifthFormFullCompatibility318.finite_pair,`FifthFormFullCompatibility318.branch_infinity,`FifthGlobalDifferential318.differential,`FifthGlobalDifferential318.restrict,`FifthGlobalDifferential318.common_restrict,`FiveInverseRootIndependence318.independent,`FifthGlobalIndependence318.raw_formula,`FifthGlobalIndependence318.independent,`FifthGlobalIndependence318.nonzero] do
    unless env.contains name do throwError "Required endpoint missing: {name}"
  let mut checked : Nat := 0
  let mut found : Nat := 0
  for idx in [:env.header.modules.size] do
    if names.contains env.header.modules[idx]!.module then
      found := found+1
      for name in env.header.moduleData[idx]!.constNames do
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Forbidden axiom {ax} in {name}"
        logInfo m!"AXIOM_CHECK {name}: {axs}"
        checked := checked+1
  unless found == 14 do throwError "Expected fourteen modules, found {found}"
  logInfo m!"FIFTH_GLOBAL_DIFFERENTIAL_AUDIT_PASS declarations={checked} modules={found}"
