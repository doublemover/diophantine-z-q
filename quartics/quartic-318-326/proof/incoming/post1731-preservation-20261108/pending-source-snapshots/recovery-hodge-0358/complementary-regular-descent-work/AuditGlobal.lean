module
import all CharacterDifferentialInvariants318
import all BranchDifferentialDivisibility318
import all BranchGlobalDifferentialRestriction318
import all ContactFiniteGlobalFunctionCoefficient318
import all CharacterCommonScalarInjection318
import all CharacterUnitChartGeneration318
import all CharacterInvariantRatioField318
import all CharacterBranchVectorFactorization318
import all CharacterOmittedBranchMultiple318
import all CharacterGlobalRegularRatio318
import all CharacterRegularDifferentialDescent318
import all CharacterGlobalDifferentialDescent318
import all CharacterGlobalScalarInjections318
import all CharacterGlobalDifferentialInjective318
import all CharacterInvariantGlobalEquiv318
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods:=#[`CharacterDifferentialInvariants318,`BranchDifferentialDivisibility318,`BranchGlobalDifferentialRestriction318,`ContactFiniteGlobalFunctionCoefficient318,`CharacterCommonScalarInjection318,`CharacterUnitChartGeneration318,`CharacterInvariantRatioField318,`CharacterBranchVectorFactorization318,`CharacterOmittedBranchMultiple318,`CharacterGlobalRegularRatio318,`CharacterRegularDifferentialDescent318,`CharacterGlobalDifferentialDescent318,`CharacterGlobalScalarInjections318,`CharacterGlobalDifferentialInjective318,`CharacterInvariantGlobalEquiv318]
  for name in #[`CharacterDifferentialInvariants318.coefficient_mem,`BranchDifferentialDivisibility318.fixed_factorization,`BranchGlobalDifferentialRestriction318.invariant_factorization,`ContactFiniteGlobalFunctionCoefficient318.raw_germ,`CharacterCommonScalarInjection318.injective,`CharacterUnitChartGeneration318.infinity_multiple,`CharacterInvariantRatioField318.ratio_range,`CharacterOmittedBranchMultiple318.section_multiple,`CharacterGlobalRegularRatio318.exists_global_ratio,`CharacterRegularDifferentialDescent318.exists_target_multiple,`CharacterGlobalDifferentialDescent318.range_pullback,`CharacterGlobalDifferentialInjective318.injective,`CharacterInvariantGlobalEquiv318.pullback_inverse,`CharacterInvariantGlobalEquiv318.invariant_normalization] do
    unless env.contains name do throwError "Missing endpoint {name}"
    liftTermElabM do
      unless ← Meta.isProp (← getConstInfo name).type do throwError "Not a proposition: {name}"
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
  unless found==15 do throwError "Expected fifteen modules, found {found}"
  logInfo m!"COMPLEMENTARY_GLOBAL_DIFFERENTIAL_DESCENT_AUDIT_PASS declarations={n} modules={found}"
