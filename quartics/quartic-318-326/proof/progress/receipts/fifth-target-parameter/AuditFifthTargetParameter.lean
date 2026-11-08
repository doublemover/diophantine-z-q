module
import all ProjectiveSwap318
import all ProjectiveSwapCharts318
import all FifthTargetParameter318
import all FifthTargetParameterRestriction318
import all FifthTargetParameterZero318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`ProjectiveSwap318,`ProjectiveSwapCharts318,`FifthTargetParameter318,`FifthTargetParameterRestriction318,`FifthTargetParameterZero318]
  for name in #[`ProjectiveSwap318.iso,`ProjectiveSwap318.map_twice,`ProjectiveSwapCharts318.chart_one,`ProjectiveSwapCharts318.chart_zero,`ProjectiveSwapCharts318.over_base,`FifthTargetParameter318.parameterIso,`FifthTargetParameter318.over_Q,`FifthTargetParameter318.finite_restriction,`FifthTargetParameterRestriction318.finite_parameter,`FifthTargetParameterRestriction318.cubic_restriction,`FifthTargetParameterRestriction318.source_infinity_restriction,`FifthTargetParameterZero318.quartic_over_t,`FifthTargetParameterZero318.zero_parameter] do
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
  logInfo m!"FIFTH_TARGET_PARAMETER_AUDIT_PASS declarations={checked} modules={found}"
