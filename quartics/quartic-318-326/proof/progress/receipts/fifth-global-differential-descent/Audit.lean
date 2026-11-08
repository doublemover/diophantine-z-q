module
import all IntrinsicChartScalarInjection318
import all FifthCommonScalarInjection318
import all GlobalScalarMultipleGluing318
import all IntrinsicChartScalarGeneration318
import all AffineGlobalFunction318
import all AffineGlobalValueNaturality318
import all ContactGlobalFunctionCoefficient318
import all FifthInvariantRatioField318
import all FifthRegularScalarDescent318
import all FifthGlobalRegularRatio318
import all FifthRegularDifferentialDescent318
import all FifthTargetDifferentialInvariants318
import all FifthGlobalDifferentialDescent318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`IntrinsicChartScalarInjection318,`FifthCommonScalarInjection318,`GlobalScalarMultipleGluing318,`IntrinsicChartScalarGeneration318,`AffineGlobalFunction318,`AffineGlobalValueNaturality318,`ContactGlobalFunctionCoefficient318,`FifthInvariantRatioField318,`FifthRegularScalarDescent318,`FifthGlobalRegularRatio318,`FifthRegularDifferentialDescent318,`FifthTargetDifferentialInvariants318,`FifthGlobalDifferentialDescent318]
  for name in #[`GlobalScalarMultipleGluing318.exists_global,`IntrinsicChartScalarGeneration318.surjective,`AffineGlobalFunction318.generic_value,`ContactGlobalFunctionCoefficient318.raw_germ,`ContactGlobalFunctionCoefficient318.genericCoefficient_smul,`FifthInvariantRatioField318.ratio_range,`FifthRegularScalarDescent318.exists_target,`FifthGlobalRegularRatio318.exists_global_ratio,`FifthRegularDifferentialDescent318.exists_target_multiple,`FifthTargetDifferentialInvariants318.fixed,`FifthGlobalDifferentialDescent318.range_pullback,`FifthGlobalDifferentialDescent318.range_average_eq_range_pullback,`FifthGlobalDifferentialDescent318.average_descends] do
    unless env.contains name do throwError "Missing endpoint {name}"
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
  unless found==13 do throwError "Expected thirteen modules, found {found}"
  logInfo m!"FIFTH_GLOBAL_DIFFERENTIAL_DESCENT_AUDIT_PASS declarations={n} modules={found}"
