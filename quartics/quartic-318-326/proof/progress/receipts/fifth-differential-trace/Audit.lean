module
import all ContactGlobalDifferentialCoefficient318
import all FifthFixingFieldEnumeration318
import all FifthDifferentialTraceComparison318
import all ContactGlobalCoefficientScalars318
import all FifthDifferentialProjection318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`ContactGlobalDifferentialCoefficient318,`FifthFixingFieldEnumeration318,
    `FifthDifferentialTraceComparison318,`ContactGlobalCoefficientScalars318,`FifthDifferentialProjection318]
  for name in #[`ContactGlobalDifferentialCoefficient318.form_restrict,
    `ContactGlobalDifferentialCoefficient318.coefficient_action,
    `ContactGlobalDifferentialCoefficient318.coefficient_signSum,
    `FifthFixingFieldEnumeration318.bijective,`FifthFixingFieldEnumeration318.sum_eq,
    `FifthDifferentialTraceComparison318.coefficient_signSum_trace,
    `FifthDifferentialTraceComparison318.generic_signSum_trace,
    `ContactGlobalCoefficientScalars318.coefficient_smul,
    `ContactGlobalCoefficientScalars318.coefficient_injective,
    `FifthDifferentialProjection318.coefficient_average,
    `FifthDifferentialProjection318.generic_average,`FifthDifferentialProjection318.average_twice] do
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
  unless found == 5 do throwError "Expected five modules, found {found}"
  logInfo m!"FIFTH_DIFFERENTIAL_TRACE_AUDIT_PASS declarations={checked} modules={found}"
